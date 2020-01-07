extern crate sdl2;
extern crate rand;
#[macro_use] extern crate yottadb;

use std::path::Path;
use std::error::Error;
use std::time::Instant;

use sdl2::pixels::{Color, PixelFormatEnum};
use sdl2::event::Event;
use sdl2::keyboard::Keycode;
use sdl2::render::{Canvas, Texture, TextureCreator};
use sdl2::surface::Surface;
use sdl2::video::WindowContext;
use sdl2::rect::Rect;

use sdl2::gfx::framerate::FPSManager;
use sdl2::gfx::primitives::DrawRenderer;

use yottadb::context_api::Context;

struct Circle<'a> {
    id: usize,
    x: i16,
    y: i16,
    r: i16,
    xvel: i16,
    yvel: i16,
    texture: Texture<'a>,
}

impl<'a> Circle<'a> {
    fn new(id: usize, x: i16, y: i16, r: i16, xvel: i16, yvel: i16, color: Color, tc: &'a TextureCreator<WindowContext>) -> Result<Circle<'a>, String> {
        let rr = (2*r) as u32 + 1;
        let surface = Surface::new(rr, rr, PixelFormatEnum::RGBA32)?;
        let surface = surface.into_canvas()?;
        surface.filled_circle(r, r, r, color)?;
        let surface = surface.into_surface();
        let texture = tc.create_texture_from_surface(surface).unwrap();
        Ok(Circle{id, x, y, r, xvel, yvel, texture})
    }

    fn new_random(ctx: &Context, id: usize, tc: &'a TextureCreator<WindowContext>) -> Result<Circle<'a>, String> {
        let (r, g, b) = (rand::random::<u8>() % 255, rand::random::<u8>() % 255, rand::random::<u8>() % 255);
        let mut key = make_ckey!(ctx, "^balls", id.to_string().as_str(), "color", "r");
        key.set(&Vec::from(r.to_string())).unwrap();
        key[3] = Vec::from(String::from("g"));
        key.set(&Vec::from(g.to_string())).unwrap();
        key[3] = Vec::from(String::from("b"));
        key.set(&Vec::from(b.to_string())).unwrap();
        Circle::new(id, (rand::random::<u16>() % 512 + 5) as i16, (rand::random::<u16>() % 512 + 5) as i16,
            (rand::random::<u16>() % 10 + 5) as i16,
            rand::random::<i16>() % 10 + 2, rand::random::<i16>() % 10 + 2,
            Color::RGB(r, g, b), tc)
    }

    fn draw<T: sdl2::render::RenderTarget>(&self, canvas: &mut Canvas<T>) -> Result<(), String> {
        let rr = (2*self.r) as u32;
        canvas.copy(&self.texture, None, Rect::new(self.x as i32, self.y as i32, rr, rr))?;
        Ok(())
    }

    fn save(&self, ctx: &Context) -> Result<(), Box<dyn Error>> {
        let mut key = make_ckey!(ctx, "^balls", self.id.to_string().as_str(), "x");
        key.set(&Vec::from(self.x.to_string()))?;
        key[2] = Vec::from("y");
        key.set(&Vec::from(self.y.to_string()))?;
        key[2] = Vec::from("xvel");
        key.set(&Vec::from(self.xvel.to_string()))?;
        key[2] = Vec::from("yvel");
        key.set(&Vec::from(self.yvel.to_string()))?;
        key[2] = Vec::from("r");
        key.set(&Vec::from(self.r.to_string()))?;
        Ok(())
    }

    fn tick<T: sdl2::render::RenderTarget>(&mut self, delta: i16, canvas: &mut Canvas<T>) -> Result<(), String> {
        let distance_x = self.xvel * delta;
        let distance_y = self.yvel * delta;
        let (canvas_width, canvas_height) = canvas.viewport().size();
        let (canvas_width, canvas_height) = (canvas_width as i16, canvas_height as i16);
        self.x += distance_x;
        if self.x < 0 {
            self.x *= -1;
            self.xvel *= -1;
        } else if self.x > canvas_width {
            self.x = canvas_width - (self.x - canvas_width);
            self.xvel *= -1;
        }
        self.y += distance_y;
        if self.y < 0 {
            self.y *= -1;
            self.yvel *= -1;
        } else if self.y > canvas_height {
            self.y = canvas_height - (self.y - canvas_height);
            self.yvel *= -1;
        }
        Ok(())
    }
}

fn main() {
    let sdl_context = sdl2::init().unwrap();
    let video = sdl_context.video().unwrap();
    let context = Context::new();

    let window = video.window("YottaDB Persistence Demo", 1024, 768)
        .position_centered()
        .build()
        .unwrap();

    let mut canvas = window.into_canvas().build().unwrap();
    let mut fps_manager = FPSManager::new();
    fps_manager.set_framerate(100).unwrap();

    let ttf_context = sdl2::ttf::init().unwrap();
    let font = ttf_context.load_font(Path::new("assets/font.ttf"), 128).unwrap();

    canvas.clear();
    canvas.present();

    let mut prev_time = Instant::now();

    let texture_creator = canvas.texture_creator();
    let mut circles: Vec<Circle> = Vec::new();

    let mut balls_key = make_ckey!(context, "^balls", "");
    for ball in balls_key.iter_key_subs() {
        let mut ball = ball.unwrap();

        let id = String::from_utf8_lossy(&ball[1]).parse::<usize>().unwrap();
        ball.push(Vec::from("x"));
        let x = ball.get().unwrap();
        let x = String::from_utf8_lossy(&x).parse::<i16>().unwrap();
        ball[2] = Vec::from("y");
        let y = ball.get().unwrap();
        let y = String::from_utf8_lossy(&y).parse::<i16>().unwrap();
        ball[2] = Vec::from("xvel");
        let xvel = ball.get().unwrap();
        let xvel = String::from_utf8_lossy(&xvel).parse::<i16>().unwrap();
        ball[2] = Vec::from("yvel");
        let yvel = ball.get().unwrap();
        let yvel = String::from_utf8_lossy(&yvel).parse::<i16>().unwrap();
        ball[2] = Vec::from("r");
        let radius = ball.get().unwrap();
        let radius = String::from_utf8_lossy(&radius).parse::<i16>().unwrap();

        ball[2] = Vec::from("color");
        ball.push(Vec::from("r"));
        let r = ball.get().unwrap();
        let r = String::from_utf8_lossy(&r).parse::<u8>().unwrap();
        ball[3] = Vec::from("g");
        let g = ball.get().unwrap();
        let g = String::from_utf8_lossy(&g).parse::<u8>().unwrap();
        ball[3] = Vec::from("b");
        let b = ball.get().unwrap();
        let b = String::from_utf8_lossy(&b).parse::<u8>().unwrap();

        circles.push(Circle::new(id, x, y, radius, xvel, yvel, Color::RGB(r, g, b), &texture_creator).unwrap());
    }
    let mut event_pump = sdl_context.event_pump().unwrap();
    'running: loop {
        canvas.set_draw_color(Color::RGB(128, 128, 128));
        canvas.clear();

        for c in &mut circles {
            c.tick(1, &mut canvas).unwrap();
            c.draw(&mut canvas).unwrap();
            c.save(&context).unwrap();
        }
        for event in event_pump.poll_iter() {
            match event {
                Event::Quit{..}|
                Event::KeyDown{ keycode: Some(Keycode::Escape), ..} => {
                    break 'running
                },
                Event::KeyDown{ keycode: Some(Keycode::N), ..} => {
                    circles.push(Circle::new_random(&context, circles.len(), &texture_creator).unwrap());
                },
                _ => {}
            }
        }

        let elapsed_time = (prev_time.elapsed().as_millis() as f64) / 1_000.0;
        prev_time = Instant::now();

        let surface = font.render(&format!("SPF: {}", elapsed_time))
            .blended(Color::RGBA(255, 0, 0, 255)).unwrap();
        let texture = texture_creator.create_texture_from_surface(&surface).unwrap();
        let fps_location = Rect::new(840, 10, 1024 - 840, 42);
        canvas.copy(&texture, None, Some(fps_location)).unwrap();

        let surface = font.render(&format!("Num Objects: {}", circles.len()))
            .blended(Color::RGBA(255, 0, 0, 255)).unwrap();
        let texture = texture_creator.create_texture_from_surface(&surface).unwrap();
        let fps_location = Rect::new(840, 40, 1024 - 840, 42);
        canvas.copy(&texture, None, Some(fps_location)).unwrap();

        canvas.present();
        fps_manager.delay();
    }
}
