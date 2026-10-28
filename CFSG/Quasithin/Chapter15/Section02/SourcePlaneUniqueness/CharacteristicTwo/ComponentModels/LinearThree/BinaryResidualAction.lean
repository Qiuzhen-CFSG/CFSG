module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.BinaryAction
public import Theory.GroupTheory.PResidual.TwoThreeComparison

/-!
# The literal cubic residual in the binary branch

The original maximal parabolic M ∩ X has an S₃ quotient over its intrinsic
two-core. It is a {2,3}-group, so its two-residual equals its prime-to-three
residual. Its Sylow two-subgroup lies in S, which identifies the join of
that residual with S as the actual parabolic-Sylow join.

The faithful NI/C_NI(V) action maps this join onto S₃. Its kernel is a
two-group: the restriction to M ∩ X has two-group kernel, and the quotient
of the join by M ∩ X is a two-group. Thus the intrinsic two-core quotient
of the join is S₃. The earlier 3′-centralizer conclusion identifies the
residual with Y₁ = O^{3′}(NI), giving the literal quotient and action clauses
used by 15.2.22. The final consumer proves the required commutator inclusion
once the distinguished complementary factor centralizes X/O₂(X).

The preliminary outside reduction and faithful action retain their earlier
owners as recorded in BinaryAction. The remaining distinguished K₂ and
K = Kc arguments stay with the linear-three branch. The 15.2.21--22 source
input is owned by qt-e-152-char2-small-actions; no inconsistent two-group
encoding of Y₁ is used here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.2.23, printed p.1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

private theorem pKernel_of_normal_restriction {A D : Type*} [Group A] [Group D]
    (f : A →* D) (B : Subgroup A) [B.Normal]
    (hquot : IsPGroup 2 (A ⧸ B)) (hk : IsPGroup 2 (f.comp B.subtype).ker) :
    IsPGroup 2 f.ker := by
  let q := (QuotientGroup.mk' B).comp f.ker.subtype
  let j : q.ker →* (f.comp B.subtype).ker :=
    { toFun := fun x => ⟨⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩,x.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : (f.comp B.subtype).ker => z.val.val) he))
  have hp := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q (hk.of_injective j hj)
  rw [comap_top] at hp
  exact hp.of_equiv topEquiv

/-- The actual parabolic has S₃ as its intrinsic two-core quotient. -/
theorem Branch.binary_parabolic_core_quotient
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F) :
    Nonempty (((M ⊓ X : Subgroup G) ⧸ pCore 2 (M ⊓ X : Subgroup G)) ≃*
      Equiv.Perm (Fin 3)) := by
  let B := (M ⊓ X).subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  obtain ⟨eP⟩ := b.binary_marked_parabolic_model
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eB := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hk
  let e := subgroupOfEquivOfLe (inf_le_right : M ⊓ X ≤ X)
  let eq := QuotientGroup.congr (pCore 2 B) (pCore 2 (M ⊓ X : Subgroup G)) e (pCore_map_iso 2 e)
  exact ⟨eq.symm.trans (eB.trans (Matrix.PSL3Two.ParabolicCoreModel.coreQuotientEquiv eP))⟩

private theorem binary_parabolic_twoThree
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F) :
    IsPiGroup twoThreePrimes (M ⊓ X : Subgroup G) := by
  obtain ⟨e⟩ := b.binary_parabolic_core_quotient
  have hc : Nat.card ((M ⊓ X : Subgroup G) ⧸ pCore 2 (M ⊓ X : Subgroup G)) = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]
    decide
  obtain ⟨r,hr⟩ := (pCore_isPGroup (p := 2) (G := (M ⊓ X : Subgroup G))).exists_card_eq
  apply (IsPiGroup_iff twoThreePrimes _).mpr
  intro p hp
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 (M ⊓ X : Subgroup G)),hc,hr] at hp
  rcases p.property.dvd_mul.mp hp with hd | hd
  · have hh : p.val ∣ 2 * 3 := hd
    rcases p.property.dvd_mul.mp hh with h2 | h3
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (p.property.dvd_of_dvd_pow hd)
      |>.resolve_left p.property.ne_one)

include d in
/-- In the binary parabolic, the literal prime-to-three residual and two-residual
agree. Adjoining the actual Sylow centralizer therefore recovers MXS. -/
theorem Branch.binary_cubic_residual_sup_sylow
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) :
    (primeToResidual 3 (M ⊓ X : Subgroup G)).map (M ⊓ X).subtype ⊔ planeSylow T ZS =
      (M ⊓ X) ⊔ planeSylow T ZS := by
  rw [← twoResidual_eq_primeToResidual_three (binary_parabolic_twoThree b)]
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  have hXI := b.input.component.1
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) b.input.component.2.subnormal
  let ei := subgroupOfEquivOfLe hXI
  let R := Q.mapSurjective (f := ei.toMonoidHom) ei.surjective
  have hS : (R : Subgroup X).map X.subtype ≤ planeSylow T ZS := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨z,hz,rfl⟩ := hy
    rw [hQ] at hz
    exact hP ▸ mem_map_of_mem I.subtype hz
  have hRM : (R : Subgroup X) ≤ (M ⊓ X).subgroupOf X := by
    intro x hx
    exact ⟨hsource.maximal.1.2 (hS (mem_map_of_mem X.subtype hx)).1,x.property⟩
  let Q0 := R.subtype hRM
  let e := subgroupOfEquivOfLe (inf_le_right : M ⊓ X ≤ X)
  let Q' := Q0.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ'S : (Q' : Subgroup (M ⊓ X : Subgroup G)).map (M ⊓ X).subtype ≤ planeSylow T ZS := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨z,hz,he⟩ := hy
    rw [← he]
    exact hS (mem_map_of_mem X.subtype hz)
  have hh := congrArg (map (M ⊓ X).subtype) (pResidual_sup_sylow_eq_top Q')
  rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype] at hh
  exact le_antisymm (sup_le_sup_right (map_subtype_le _) _)
    (sup_le (hh.symm.le.trans (sup_le le_sup_left (hQ'S.trans le_sup_right))) le_sup_right)

private theorem kernel_two_of_symmetric_three_core_quotient
    {A : Type*} [Group A] [Finite A]
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (f : A →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f) :
    IsPGroup 2 f.ker := by
  have hs : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hc : Nat.card A = 6 * Nat.card (pCore 2 A) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),Nat.card_congr e.toEquiv,hs]
  have hk := f.ker.index_mul_card
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,hs,hc] at hk
  have he : Nat.card f.ker = Nat.card (pCore 2 A) := by omega
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  exact IsPGroup.of_card (he.trans hn)

include d in
/-- The genuine parabolic-Sylow join has S₃ as its two-core quotient. -/
theorem Branch.binary_parabolic_join_quotient
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    Nonempty ((((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G) ⧸
      pCore 2 ((M ⊓ X) ⊔ planeSylow T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let J := (M ⊓ X) ⊔ planeSylow T ZS
  let A := (M ⊓ X).subgroupOf J
  have hIX := b.binary_normal_of_action d hI hout f hker
  have hSNI : planeSylow T ZS ≤ M ⊓ I :=
    le_inf (inf_le_left.trans hsource.maximal.1.2)
      ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right)
  have hJNI : J ≤ M ⊓ I := sup_le (inf_le_inf_left M b.input.component.1) hSNI
  let g := f.comp (inclusion hJNI)
  have hAg : Function.Surjective (g.comp A.subtype) := by
    intro y
    have hh : y ∈ ((M ⊓ X).subgroupOf (M ⊓ I)).map f := by
      rw [b.binary_parabolic_action_full d hI hout f hker]
      trivial
    obtain ⟨x,hx,he⟩ := hh
    exact ⟨⟨⟨x.val,(le_sup_left : M ⊓ X ≤ J) hx⟩,hx⟩,he⟩
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x,hx⟩ := hAg y
    exact ⟨x.val,hx⟩
  have hn : J ≤ normalizer (M ⊓ X : Set G) :=
    (le_inf (hJNI.trans (inf_le_left.trans M.le_normalizer))
      (hJNI.trans (inf_le_right.trans hIX))).trans inf_normalizer_le_normalizer_inf
  let : A.Normal := normal_subgroupOf_of_le_normalizer hn
  have hquot : IsPGroup 2 (J ⧸ A) := by
    apply isPGroup_quotient_of_sup_eq_top A ((planeSylow T ZS).subgroupOf J)
      ((T.isPGroup'.to_le inf_le_left).comap_subtype)
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right,
      ← MonoidHom.range_eq_map,range_subtype]
  obtain ⟨eMX⟩ := b.binary_parabolic_core_quotient
  let e := subgroupOfEquivOfLe (show M ⊓ X ≤ J from le_sup_left)
  let eA := (QuotientGroup.congr (pCore 2 A) (pCore 2 (M ⊓ X : Subgroup G))
    e (pCore_map_iso 2 e)).trans eMX
  have hgker := pKernel_of_normal_restriction g A hquot
    (kernel_two_of_symmetric_three_core_quotient eA (g.comp A.subtype) hAg)
  have hk := ker_eq_twoCore_of_surjective_perm_three g hg hgker
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

include d in
/-- The literal Y₁ = O^{3′}(NI) has the S₃ quotient required by 15.2.22;
Y₁ is not assumed to be a two-group. -/
theorem Branch.binary_source_residual_quotient
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hcentral : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G))) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    Nonempty (((Y ⊔ planeSylow T ZS : Subgroup G) ⧸
      pCore 2 (Y ⊔ planeSylow T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  dsimp only
  rw [b.binary_cubic_residual_eq_of_action d hI hout f hker hcentral,
    b.binary_cubic_residual_sup_sylow d hI]
  exact b.binary_parabolic_join_quotient d hI hout f hker


include d in
/-- All residual and action clauses needed for the final 15.2.22 application.
The earlier 3′-centralizer conclusion remains explicit. -/
theorem Branch.binary_source_residual_data
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hcentral : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G))) :
    let K := (pResidual 2 H).map H.subtype
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    Y ≤ M ⊓ I ∧ IsPPerfect 2 Y ∧ planeSylow T ZS ≤ normalizer (Y : Set G) ∧
      Nonempty (((Y ⊔ planeSylow T ZS : Subgroup G) ⧸
        pCore 2 (Y ⊔ planeSylow T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ IsSmallActionIrreducible (planeSylow T ZS) K := by
  obtain ⟨hy,hp,hn⟩ := intersection_cubic_residual_basics d hI
  exact ⟨hy,hp,hn,b.binary_source_residual_quotient d hI hout f hker hcentral,
    b.binary_reducible_of_normalized d hI (b.binary_sylow_normalizes d hI hout f hker)⟩

include d in
/-- Apply the constructed binary action and residual identity to the literal
final commutator. Identification and core-centralization of the distinguished
K₂ are still required from the binary factor geometry. -/
theorem Branch.binary_commutator_of_action
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F)
    (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    (hcentral : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    {K₂ : Subgroup G} (hSK₂ : planeSylow T ZS ≤ normalizer (K₂ : Set G))
    (hp : IsPPerfect 2 K₂) (hc : ⁅X,K₂⁆ ≤ X.pCoreIn 2) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    ⁅Y,K₂⁆ ≤ Y ⊓ K₂ :=
  b.intersection_cubic_residual_commutator_le d hI
    (b.binary_normal_of_action d hI hout f hker) hSK₂ hp hc
    (b.binary_cubic_residual_eq_of_action d hI hout f hker hcentral)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
