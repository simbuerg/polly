; RUN: opt %loadPolly -polly-allow-nonaffine -polly-dce -polly-ast -analyze < %s | FileCheck %s
;
; CHECK: for (int c1 = 0; c1 <= 1023; c1 += 1)
;
;    void f(int *A) {
;      for (int i = 0; i < 1024; i++)
;        A[i % 2] = i;
;    }
;
target datalayout = "e-m:e-p:32:32-i64:64-v128:64:128-n32-S64"

define void @f(i32* %A) {
entry:
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %i.0 = phi i32 [ 0, %entry ], [ %inc, %for.inc ]
  %exitcond = icmp ne i32 %i.0, 1024
  br i1 %exitcond, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %rem = srem i32 %i.0, 2
  %arrayidx = getelementptr inbounds i32* %A, i32 %rem
  store i32 %i.0, i32* %arrayidx, align 4
  br label %for.inc

for.inc:                                          ; preds = %for.body
  %inc = add nsw i32 %i.0, 1
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret void
}

