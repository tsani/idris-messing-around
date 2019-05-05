applyVar (weaken (weaken (id k))) x = FS (FS x)

I need to restructure this to get an FS on the head of the LHS, then I can use
cong ih.
Perhaps I can use the rencomp lemma, since weaken is a renaming.

Recall that weakening on term `t` is `apply (weaken (id _)) t`.
Ultimately, I'm trying to show that this just FS's all the variables.

so applyVar (weaken (id k)) x = FS x
is really trying to show that
applyVar (apply (weaken (id _)) (id k)) x = FS x
Perhaps this can actually be done with relative ease by induction on k?

Okay, why was I even trying to prove this anyway?

How about proving that an identity renaming upgrades to an identity substitution
for variables?
Aha, well if I actually proved that lemma applyVarWeakenIsFS, then I could use
it to change the proof goal of this lemma:
now it is `var (FS x) = applyVar (weaken (id k)) x`.
If I prove a similar lemma for substitutions, I can show that
`applyVar (weaken (id k)) x = var (FS x)`. Then I'm in business.

But for some reason, Idris won't let me rewrite this lemma.

Okay, the key is the renaming composition lemma. I think that if I prove this
I'm in business.

For a renaming `s : k -> n` and a renaming `r : j -> k`,
`[s][r]t` = `[s.r]t`, where `.` is composition of renamings.
`(s . r)` is defined by induction on `r`.

### Theorem (Renaming Composition Lemma)

If `s : Renaming n k` and `r : Renaming k j`

Now the renaming composition lemma is ultimately a lemma about application of
substitutions, so we prove it by induction on the term `t`.

* _case_ `t = Lam t'`.
  WTS: `apply s (apply r (Lam t')) = apply (s . r) (Lam t')`.
  By def of `apply r`,
  WTS: `apply s (Lam (apply (extend r) t')) = apply (s . r) (Lam t')`.
  WTS: `Lam (apply (extend s) (apply (extend r) t'))
        = Lam (apply (extend (s . r))) t'`
  by congruence, it suffices to show
  `apply (extend s) (apply (extend r) t') = apply (extend (s . r)) t'`.
  By induction hypothesis, it suffices to show
  `apply (extend s . extend r) t' = apply (extend (s . r)) t'`
  To complete the proof, we need to show that
  `extend s . extend r = extend (s . r)`.
  
### Theorem (Extend Distributes Lemma)

If `s : Renaming n k` and `r : Renaming k j`, then
`extend (s . r) = extend s . extend r`.

Proof by induction on `r`.

* _case_ `r = Weaken`.
  WTS `extend (s . Weaken) = extend s . extend Weaken`.
  By definition of extend, WTS:
  `extend Weaken = extend s . (weaken Weaken :: FZ)`
  By definition of extend, WTS:
  `weaken Weaken :: FZ = extend s . (Weaken :: FZ)`
  By definition of `.`, WTS:
  `Weaken :: FZ = extend s . Weaken :: (applyVar (extend s) FZ)`
  By def. of `extend`, WTS:
  `Weaken :: FZ = extend s . Weaken :: (applyVar (weaken s :: FZ) FZ)`.
  By def. of `applyVar`, WTS:
  `Weaken :: FZ = extend s . Weaken :: FZ`.
  By def. of `.`, WTS:
  `Weaken :: FZ = Weaken :: FZ`.
  This holds by reflexivity.
  
* _case_ `r = r' :: f`.
  WTS: `extend (s . (r' :: f)) = extend s . extend (r' :: f)`
  By definition of `.`, WTS:
  `extend (s . r' :: applyVar s f) = extend s . extend (r' :: f)`
  Expanding the definition of `extend`, WTS:
  `weaken (s . r' :: applyVar s f) :: FZ = (weaken s :: FZ) . (weaken (r' :: f) :: FZ)`
  By definition of `.` on the RHS, WTS:
  `weaken (s . r' :: applyVar s f) :: FZ
   = (weaken s :: FZ) . (weaken (r' :: f)) :: applyVar (weaken s :: FZ) FZ`.
  By definition of `applyVar` on the RHS, WTS:
  `weaken (s . r' :: applyVar s f) :: FZ
   = (weaken s :: FZ) . (weaken (r' :: f)) :: FZ`
  By congruence, it suffices to show: 
  `weaken (s . r' :: applyVar s f) = (weaken s :: FZ) . (weaken (r' :: f))`
  (we "cancelled" `:: FZ` on both sides)
  By definition of `weaken` on the RHS, WTS:
  `weaken (s . r' :: applyVar s f) = (weaken s :: FZ) . (weaken r' :: FS f)`
  By definition of `.` on the RHS, WTS:
  `weaken (s . r' :: applyVar s f)
   = (weaken s :: FZ) . (weaken r') :: applyVar (weaken s :: FZ) (FS f)`
  By definition of `applyVar` on the RHS, WTS:
  `weaken (s . r' :: applyVar s f)
   = (weaken s :: FZ) . (weaken r') :: applyVar (weaken s) f`
  By definition of `weaken` on the LHS, WTS:
  `weaken (s . r') :: FS (applyVar s f)
   = (weaken s :: FZ) . (weaken r') :: applyVar (weaken s) f`.
  By lemma `applyVarWeaken`, we know that
  `applyVar (weaken s) f = FS (applyVar s f)`, so WTS:
  `weaken (s . r') :: FS (applyVar s f)
   = (weaken s :: FZ) . (weaken r') :: FS (applyVar s f)`.
  By congruence, WTS:
  `weaken (s . r') = extend s . weaken r'


### Theorem

If `s : Subst n k` and `i : Fin k`, then
`applyVar (weaken s) i = weaken (applyVar s i)`.

Proof by induction on `s` and `i`.

* _case_ `i = FZ`.
  WTS: applyVar (weaken s) FZ = weaken (applyVar s FZ)
  
### Theorem

If `i : Fin k`, then
`applyVar (id k) i = Var i`.

Proof by induction on `i`.

* _case_ `i = FZ`.
  Then `k = S k'`.
  WTS: `applyVar (id (S k')) FZ = Var FZ`.
  By definition of `id`, WTS:
  `applyVar (extend (id k')) FZ = Var FZ`.
  By definition of `extend`, WTS:
  `applyVar (weak'en (id k') :: Var FZ) FZ = Var FZ`
  By definition of `applyVar`, WTS:
  `Var FZ = Var FZ`.
  This holds by reflexivity.
* _case_ `i = FS i'`.
  Then `k = S k'`.
  WTS: `applyVar (id (S k')) (FS i') = Var (FS i')`
  By definition of `id`, WTS:
  `applyVar (extend (id k')) (FS i') = Var (FS i')`.
  By definition of `extend`, WTS:
  `applyVar (weaken (id k') :: Var FZ) (FS i') = Var (FS i')`.
  By definition of `applyVar`, WTS:
  `applyVar (weaken (id k')) i' = Var (FS i')`.
  By lemma `applyVarWeaken`, we hoist the weakening out, so WTS:
  `weaken (applyVar (id k') i') = Var (FS i')`.
  By IH, WTS:
  `weaken (Var i') = Var (FS i')`.
  By lemma `applyWeaken`, WTS:
  `Var (FS i') = Var (FS i')`, which holds by reflexivity.
  
### Theorem

If `s : Subst n k` and `i : Fin k`, then
`applyVar (weaken s) i = weaken (applyVar s i)`.

Proof by induction on `s` and `i`.

* _case_ `s = Weaken`.
  Then `k = 0`, so `i : Fin 0`.
  But `Fin 0` is uninhabited, so this case is impossible.

* _case_ `s = s' :: t`.
  * _subcase_ `i = FZ`.
    WTS: `applyVar (weaken (s' :: t)) FZ = weaken (applyVar (s' :: t) FZ)`.
    By definition of of `weaken` on the LHS, WTS:
    `applyVar (weaken s' :: weaken t) FZ = weaken (applyVar (s' :: t) FZ)`.
    By definition of `applyVar` on both sides, WTS:
    `weaken t = weaken t`, which holds by reflexivity.
  * _subcase_ `i = FS i'`.
    WTS: `applyVar (weaken (s' :: t)) (FS i') = weaken (applyVar (s' :: t) (FS i')`.
    By definition of `weaken` on the LHS, WTS:
    `applyVar (weaken s' :: weaken t) (FS i') = weaken (applyVar (s' :: t) (FS i')`.
    By definition of `applyVar`, WTS:
    `applyVar (weaken s') i' = weaken (applyVar s' i')`, which holds by IH.
    
### Theorem (Substitution Extension Lemma)

For any substitutions `s : Subst n k` and `r : Subst k j`,
`extend s . extend r = extend (s . r)`.

Proof by induction on `r`.

* _case_ `r = Weaken`.
  WTS: `extend s . extend Weaken = extend (s . Weaken)`.
  By definition of `.`, WTS:
  `extend s . extend Weaken = extend Weaken`
  By defintion of `extend`, WTS:
  `extend s . (weaken Weaken :: FZ) = weaken Weaken :: FZ`.
  By definition of `.`, WTS:
  `extend s . weaken Weaken :: FZ = weaken Weaken :: FZ`.
  By definition of `Weaken`, WTS:
  `extend s . Weaken :: FZ = Weaken :: FZ`.
  By definition of `.`, WTS:
  `Weaken :: FZ = Weaken :: FZ`, which holds by reflexivity.
  
* _case_ `r = r' :: t`.
  WTS: `extend s . extend (r' :: t) = extend (s . (r' :: t))`.
  By definition of `.` on the RHS:
  `extend s . extend (r' :: t) = extend (s . r' :: apply s t)`.
  By definition of `extend`, WTS:
  `extend s . (weaken (r' :: t) :: FZ) = weaken (s . r' :: apply s t) :: FZ`.
  By definition of `weaken`, WTS:
  `extend s . (weaken r' :: weaken t :: FZ)
   = weaken (s . r') :: weaken (apply s t) :: FZ`.


### Theorem (Substitution Composition Lemma)

`apply s (apply r t) = apply (s . r) t`.

Proof by induction on `t`.

* _case_ `t = Lam t'`.
  WTS `apply s (apply r (Lam t')) = apply (s . r) (Lam t')`.
  By definition of `apply`, WTS:
  `apply s (Lam (apply (extend r) t')) = Lam (apply (extend (s . r)) t')`.
  By definition of `apply`, WTS:
  `Lam (apply (extend s) (apply (extend r) t')) = Lam (apply (extend (s . r)) t')`.
  By congruence, WTS:
  `apply (extend s) (apply (extend r) t') = apply (extend (s . r)) t'`.
  Instantiating the IH with `s = extend s`, `r = extend r`, `t = t'`, we get
  `apply (extend s) (apply (extend r) t') = apply (extend s . extend r) t'`.
  So it suffices to show that `extend (s . r) = extend s . extend r`.
  This holds by the Substitution Extension Lemma.


### Theorem (Fundamental Lemma)

If `g |- (t, a)`, then `g |= (t, a)`.

Proof by induction on the typing derivation `g |- (t, a)`.

Case `Lam t'`.
Then `a = a1 ~> a2`.

By induction hypothesis, `g |- (t', a2)` implies `g |= (t', a2)`.

WTS: `g |= (t, a)`,
i.e. forall `k`, forall `s` such that `G k s g`, if `apply s t`
