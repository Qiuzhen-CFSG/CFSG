module
public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Complementary fixed factors for a faithful elementary-nine action

Let an elementary abelian group A of order nine act faithfully on an
elementary abelian group V of order sixteen, with no nonidentity point
fixed by all of A. There are complementary actor subgroups K,L of order
three whose fixed subgroups each have order four and complement one
another in V. The original supplied action is used throughout; no ambient
permutation action or choice of isotypic coordinates is needed.

Coprime abelian fixed-point generation reduces to actor lines of order
three. Every line-fixed subgroup is A-invariant. Orbit counting modulo
three, together with its order dividing sixteen, makes each nontrivial
one have order four or sixteen; faithfulness excludes sixteen. Generation
therefore supplies two distinct active lines. They generate A, so their
fixed groups intersect trivially, and their product has all sixteen points.

This is the factor choice in Stellmacher (10.1), after (18), printed p.64,
for the actual elementary-nine odd residual acting on the terminal module
quotient. The caller supplies that faithful quotient action and its trivial
full fixed subgroup.
-/

open scoped IsMulCommutative

private theorem three_lines_complement
    {A:Type*} [Group A] [Finite A] [IsElementaryAbelian 3 A]
    (hA:Nat.card A=9) (K L:Subgroup A)
    (hK:Nat.card K=3) (hL:Nat.card L=3) (hne:K≠L) : IsCompl K L := by
  have hdiv : Nat.card (K⊓L:Subgroup A) ∣ 3 := hK ▸ Subgroup.card_dvd_of_le inf_le_left
  have hinf : K⊓L=⊥ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hone|hthree
    · exact Subgroup.card_eq_one.mp hone
    · have heqK : K⊓L=K:=Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hK,hthree])
      have heqL : K⊓L=L:=Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hL,hthree])
      exact (hne (heqK.symm.trans heqL)).elim
  have hprod:=Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes K L
    (by rw [Subgroup.normalizer_eq_top];exact le_top)
  rw [hK,hL,hinf,Subgroup.card_bot,one_mul] at hprod
  have htop : K⊔L=⊤ := Subgroup.eq_of_le_of_card_ge le_top (by
    rw [Subgroup.card_top,hA,←hprod])
  exact IsCompl.of_eq hinf htop

private theorem nontrivial_line_fixed_card_four
    {A V:Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 3 A] [IsElementaryAbelian 2 V]
    [MulDistribMulAction A V] [FaithfulSMul A V]
    (hV:Nat.card V=16) (hfixed:FixedPoints.subgroup (⊤:Subgroup A) V=⊥)
    (K:Subgroup A) (hK:Nat.card K=3) (hne:FixedPoints.subgroup K V≠⊥) :
    Nat.card (FixedPoints.subgroup K V)=4 := by
  let C:=FixedPoints.subgroup K V
  have hstable (a:A) (v:V) (hv:v∈C) : a • v ∈ C := by
    intro k
    change (k:A) • (a • v)=a • v
    rw [←mul_smul,mul_comm (k:A),mul_smul]
    exact congrArg (fun w:V=>a • w) (hv k)
  let _ : IsInvariant A V C := ⟨fun a v=>⟨hstable a v,fun h=>by
    have hh:=hstable a⁻¹ (a • v) h
    simpa only [inv_smul_smul] using hh⟩⟩
  have hfixedC : FixedPoints.subgroup A C=⊥ := by
    apply bot_unique
    intro c hc
    change c=1
    apply Subtype.ext
    have hh : (c:V)∈FixedPoints.subgroup (⊤:Subgroup A) V := by
      intro a
      exact congrArg (fun z:C=>(z:V)) (hc (a:A))
    exact hfixed.le hh
  have hmod:=(IsElementaryAbelian.isPGroup 3 A).card_modEq_card_fixedPoints C
  change Nat.ModEq 3 (Nat.card C) (Nat.card (FixedPoints.subgroup A C)) at hmod
  rw [hfixedC,Subgroup.card_bot] at hmod
  have hnot16 : Nat.card C≠16 := by
    intro hc
    have htop : C=⊤:=Subgroup.eq_of_le_of_card_ge le_top (by rw [Subgroup.card_top,hV,hc])
    have hKbot : K=⊥:=by
      apply bot_unique
      intro a ha
      change a=1
      apply FaithfulSMul.eq_of_smul_eq_smul (α:=V)
      intro v
      have hv : v∈C:=htop.ge (Subgroup.mem_top v)
      simpa only [one_smul,Subgroup.smul_def] using hv ⟨a,ha⟩
    have hh:=hK
    rw [hKbot,Subgroup.card_bot] at hh
    omega
  have hdiv : Nat.card C ∣ 2^4:=by
    change Nat.card C ∣ 16
    rw [←hV]
    exact Subgroup.card_subgroup_dvd_card C
  obtain ⟨n,hn,hcard⟩:=(Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  interval_cases n
  · exact (hne (Subgroup.card_eq_one.mp hcard)).elim
  · change Nat.card C=2 at hcard
    rw [hcard] at hmod
    norm_num [Nat.ModEq] at hmod
  · exact hcard
  · change Nat.card C=8 at hcard
    rw [hcard] at hmod
    norm_num [Nat.ModEq] at hmod
  · exact (hnot16 hcard).elim

public theorem nine_sixteen_fixed_factor_decomposition
    {A V:Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 3 A] [IsElementaryAbelian 2 V]
    [MulDistribMulAction A V] [FaithfulSMul A V]
    (hA:Nat.card A=9) (hV:Nat.card V=16)
    (hfixed:FixedPoints.subgroup (⊤:Subgroup A) V=⊥) :
    ∃ K L:Subgroup A, Nat.card K=3 ∧ Nat.card L=3 ∧ IsCompl K L ∧
      Nat.card (FixedPoints.subgroup K V)=4 ∧
      Nat.card (FixedPoints.subgroup L V)=4 ∧
      IsCompl (FixedPoints.subgroup K V) (FixedPoints.subgroup L V) := by
  classical
  let _ : CommGroup A:=IsMulCommutative.instCommGroup
  let _ : CommGroup V:=IsMulCommutative.instCommGroup
  let _ : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 V):=⟨IsElementaryAbelian.isPGroup 2 V⟩
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G:=V) (A:=A) (q:=2) (by rw [hA];decide)
  have hlines : (⨆ (K:Subgroup A) (_:Nat.card K=3), FixedPoints.subgroup K V)=⊤ := by
    apply top_unique
    rw [←hgen]
    refine iSup₂_le fun K hcyc=>?_ 
    have hdiv : K.index∣3:=by
      rw [Subgroup.index_eq_card,←hcyc.exponent_eq_card]
      exact (Group.exponent_quotient_dvd K).trans (IsElementaryAbelian.exponent_dvd_p 3 A)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hone|hthree
    · rw [Subgroup.index_eq_one.mp hone,hfixed]
      exact bot_le
    · have hKcard : Nat.card K=3:=by
        have hh:=K.index_mul_card
        rw [hthree,hA] at hh
        omega
      exact le_iSup_of_le K (le_iSup_of_le hKcard le_rfl)
  have hchoose (H:Subgroup V) (hH:H≠⊤) :
      ∃ K:Subgroup A, Nat.card K=3 ∧ ¬FixedPoints.subgroup K V≤H := by
    by_contra hn
    push Not at hn
    apply hH
    apply top_unique
    rw [←hlines]
    exact iSup₂_le fun K hK=>hn K hK
  have hVnontrivial : (⊥:Subgroup V)≠⊤:=by
    intro hh
    have hc:=congrArg (fun H:Subgroup V=>Nat.card H) hh
    rw [Subgroup.card_bot,Subgroup.card_top,hV] at hc
    omega
  obtain ⟨K,hK,hKnot⟩:=hchoose ⊥ hVnontrivial
  have hKne : FixedPoints.subgroup K V≠⊥:=fun h=>hKnot h.le
  have hKcard:=nontrivial_line_fixed_card_four hV hfixed K hK hKne
  have hKproper : FixedPoints.subgroup K V≠⊤:=by
    intro htop
    rw [htop,Subgroup.card_top,hV] at hKcard
    omega
  obtain ⟨L,hL,hLnot⟩:=hchoose (FixedPoints.subgroup K V) hKproper
  have hLne : FixedPoints.subgroup L V≠⊥:=by
    intro hbot
    exact hLnot (hbot ▸ bot_le)
  have hLcard:=nontrivial_line_fixed_card_four hV hfixed L hL hLne
  have hKL : K≠L:=by intro h;subst L;exact hLnot le_rfl
  have hcompl:=three_lines_complement hA K L hK hL hKL
  have hinf : FixedPoints.subgroup K V⊓FixedPoints.subgroup L V=⊥:=by
    apply bot_unique
    intro v hv
    have hKst : K≤MulAction.stabilizer A v:=fun a ha=>hv.1 ⟨a,ha⟩
    have hLst : L≤MulAction.stabilizer A v:=fun a ha=>hv.2 ⟨a,ha⟩
    have htop : (⊤:Subgroup A)≤MulAction.stabilizer A v:=
      hcompl.sup_eq_top ▸ sup_le hKst hLst
    have hh : v∈FixedPoints.subgroup (⊤:Subgroup A) V:=fun a=>htop a.property
    exact hfixed.le hh
  have hprod:=Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (FixedPoints.subgroup K V) (FixedPoints.subgroup L V)
      (by rw [Subgroup.normalizer_eq_top];exact le_top)
  rw [hKcard,hLcard,hinf,Subgroup.card_bot,one_mul] at hprod
  have htop : FixedPoints.subgroup K V⊔FixedPoints.subgroup L V=⊤:=
    Subgroup.eq_of_le_of_card_ge le_top (by rw [Subgroup.card_top,hV,←hprod])
  exact ⟨K,L,hK,hL,hcompl,hKcard,hLcard,IsCompl.of_eq hinf htop⟩
