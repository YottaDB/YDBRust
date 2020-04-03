/****************************************************************
*                                                               *
* Copyright (c) 2019-2020 YottaDB LLC and/or its subsidiaries.  *
* All rights reserved.                                          *
*                                                               *
*       This source code contains the intellectual property     *
*       of its copyright holder(s), and is made available       *
*       under a license.  If you do not know the terms of       *
*       the license, please stop and do not read further.       *
*                                                               *
****************************************************************/

#include "libyottadb.h"

#define MAXVPARMS 36

// TODO: this struct will be updated in the YDB 1.32 release!
typedef struct gparam_list_struct {
    intptr_t  n;
    void *arg[MAXVPARMS];
} gparam_list;
