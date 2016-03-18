/*
 * Copyright (C) 2009 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */
#include <stdio.h>
#include <string.h>
#include <jni.h>

/* This is a trivial JNI example where we use a native method
 * to return a new VM String. See the corresponding Java source
 * file located at:
 *
 *   apps/samples/hello-jni/project/src/com/example/HelloJni/HelloJni.java
 */

char *inptr0;
char *inptr;
char inbuf[1000];
char outbuf[1000];
char *outptr;

char buf[1000];

char inputchar (void)
{
 return *inptr++;
}

void output (char *s)
{
 strcpy (outptr, s);
 outptr += strlen(s);
}

extern void cvm(int) ;

JNIEnv *genv;
jobject gobj;

void checkcode (void);

jmethodID mid_trace;

int init_trace (void)
{
	jclass cls = (*genv)->GetObjectClass (genv, gobj);
	mid_trace = (*genv)->GetMethodID (genv, cls, "trace", "(Ljava/lang/String;)I");
	if (!mid_trace)
		exit(0);
}

int trace1 (char *s)
{
	jint x;
	x = (*genv)->CallIntMethod (genv, gobj, mid_trace, (*genv)->NewStringUTF(genv,s)); 
	return (int)x;
}


int trace (char *s) 
{ 

 trace1(s) ;
/* 
 checkcode() ; 
*/ 
 return 0; 
} 

#define DRAW_SIZE 1000
#define NPDRAW 14

#define DRAW_END 0
#define DRAW_POINT 1
#define DRAW_CLEAR 2
#define DRAW_CIRCLE 3

struct draw
{
 int op, color;
 int p[NPDRAW];
};

int ndraws;
struct draw draw_table[DRAW_SIZE];

void reset_draw (void)
{
 trace ("reset_draw");
 ndraws = 0;
}

void draw (int op, int color, int np, int *p)
{
int i;
 trace ("draw");
 draw_table[ndraws].op = op;
 draw_table[ndraws].color = color;
 for (i=0; i<np && i<NPDRAW; i++) 
  draw_table[ndraws].p[i] = p[i];
 ndraws++;
}

void invalidate_view (void)
{
	trace ("jni invalidate");
	jclass cls = (*genv)->GetObjectClass (genv, gobj);
	jmethodID mid = (*genv)->GetMethodID (genv, cls, "invalidate_view", "()V");
	(*genv)->CallIntMethod (genv, gobj, mid); 
}

jint Java_jacquesb_cvm_cvm_getdrawnbr (JNIEnv *env, jobject thiz)
{
 return (jint)ndraws;
}

jint Java_jacquesb_cvm_cvm_getdrawop (JNIEnv* env, jobject thiz, jint i)
{
 if (i >= ndraws)
  return (jint) DRAW_END;
 else
  return (jint) (draw_table[i].op);
}

jint Java_jacquesb_cvm_cvm_getdrawcolor (JNIEnv* env, jobject thiz, jint i)
{
 return (jint) (draw_table[i].color);
}

jint Java_jacquesb_cvm_cvm_getdrawparam (JNIEnv* env, jobject thiz, jint i, jint j)
{
 return (jint) (draw_table[i].p[j]);
}

jint Java_jacquesb_cvm_cvm_jnidraw (JNIEnv* env, jobject thiz, jobject canvas, jobject paint)
{
int i;
jclass cls_canvas, cls_paint;
jmethodID mid, mid_setcolor;
float x, y, r;
jfloat jx, jy, jr;
 cls_canvas = (*env)->FindClass (env, "android/graphics/Canvas");
 cls_paint = (*env)->FindClass (env, "android/graphics/Paint");
 mid_setcolor = (*env)->GetMethodID (env, cls_paint, "setColor", "(I)V");
 for (i=0; i<ndraws; i++)
 {
  switch (draw_table[i].op)
  {
   case DRAW_POINT:
    mid = (*env)->GetMethodID (env, cls_canvas, "drawPoint", "(F,F,Landroid/graphics/Paint;)V");
    (*env)->CallVoidMethod (env, paint, mid_setcolor, (jint)(draw_table[i].color));
    x = (float)(draw_table[i].p[0]);
    y = (float)(draw_table[i].p[1]);
    jx = (jfloat)x;
    jy = (jfloat)y;
    (*env)->CallVoidMethod (env, canvas, mid, jx, jy, paint);
    break;
   case DRAW_CIRCLE:
    mid = (*env)->GetMethodID (env, cls_canvas, "drawCircle", "(F,F,F,Landroid/graphics/Paint;)V");
    (*env)->CallVoidMethod (env, paint, mid_setcolor, (jint)(draw_table[i].color));
    x = (float)(draw_table[i].p[0]);
    y = (float)(draw_table[i].p[1]);
    r = (float)(draw_table[i].p[2]);
    jx = (jfloat)x;
    jy = (jfloat)y;
    jr = (jfloat)r;
    (*env)->CallVoidMethod (env, canvas, mid, jx, jy, jr, paint);
    break;
   default:
    break;
  }
 }
 return (jint)0;
}

jint Java_jacquesb_cvm_cvm_init ( JNIEnv* env, jobject thiz )
{
 jint r;
 genv = env;
 gobj = thiz;

 init_trace();

 /* trace ("Hello"); */

 r = (jint)0;
 initialize();
 reset_draw();
 trace ("after init");
 return r;
}

int first = 1;

jstring Java_jacquesb_cvm_cvm_jni ( JNIEnv* env, jobject thiz, jstring jinput )
{
    char *cinput;
    int i, j;
    int p[NPDRAW];
    // return (*env)->NewStringUTF(env, "Hello from JNI !");
    genv = env;
    gobj = thiz;
    /* trace ("jni"); */

    cinput = (*env)->GetStringUTFChars(env,jinput,0);
    sprintf (inbuf, " %s ", cinput);
    inptr0 = inbuf;
    inptr = inptr0;
    outptr = outbuf;

    /* reset_draw(); */

    /* trace ("before cvm"); */
    cvm (first);
    trace ("after cvm");

    *outptr = 0;
    first = 0;
/*
    for (i=40; i<55; i++)
    for (j=40; i<50; j++)
    {
      p[0] = i;
      p[1] = j;
      draw (DRAW_POINT, 0x123456 + 0x10000*i + j, 2, p);
    }
*/
/*
    p[0] = 80;
    p[1] = 50;
    p[2] = 10;
    draw (DRAW_CIRCLE, 0xFF123456, 3, p);

    invalidate_view();
*/
    return (*env)->NewStringUTF (env, outbuf);
}


