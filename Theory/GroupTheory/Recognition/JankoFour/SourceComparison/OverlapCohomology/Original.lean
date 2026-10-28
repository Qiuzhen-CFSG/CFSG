module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology.Automorphisms
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.PlaneOverlaps
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Defs
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility

/-!
# The original overlap quotient and its complete automorphism calculation

Map the genuine native outer hexad group into Aut(M22), recognize its
order-11520 image as a hexad stabilizer, and conjugate that hexad to the
specified original one. Composing with the literal source cubic projection
gives an isomorphism I/(Q A) to that native group. All natural-module
coordinates and quotient maps are transported through this same map.

The full Sp4(2) H1 calculation and the native automorphism classification
therefore apply to the original quotient: every automorphism is inner,
optionally followed by the constructed outer involution. The denominator
identity explicitly retains A, the original cubic scalar. No independent
isomorphism, compatible-map witness, or automorphism classification is an
input. This is the quotient part of AS91 (8.2), p.606; lifting it to I and
matching the source Todd twist are further obligations.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
open Subgroup Representation Representation.OneCohomology
open Representation.OneCohomology.SymplecticFour
open Sporadic.Mathieu Sporadic.Mathieu.M22ValueBound.Concrete
open Sporadic.Mathieu.M22ChapterH.Hexad.Action
open LocalGeometry LocalGeometry.LocalSubgroups SourceRecognition
open scoped Pointwise

private theorem native_card : Nat.card Outer = 11520 := by
  have hc : Nat.card (pCore 2 Outer) = 16 := by
    rw [Nat.card_congr nativeCoordinates.toEquiv]
    change Nat.card V = 16
    simp [V,Nat.card_eq_fintype_card]
  have hi : (pCore 2 Outer).index = 720 := by
    change Nat.card (Outer ⧸ pCore 2 Outer) = _
    rw [Nat.card_congr Natural.outerMarking.toEquiv,Nat.card_perm,Nat.card_fin]
    decide
  rw [←(pCore 2 Outer).card_mul_index,hc,hi]

private noncomputable def pairDesignEquiv : MathieuCode.m22PairStabilizer ≃* m22DesignAut :=
  MathieuCode.m22PairStabilizerEquivAut.trans designAutEquiv.symm

/-- Place the genuine native hexad group at the specified source hexad. -/
theorem exists_native_hexad_equiv (B : Finset (Fin 22)) (hB : B ∈ m22Blocks) :
    Nonempty (Outer ≃* designStabilizer B) := by
  let R := Outer.map pairDesignEquiv.toMonoidHom
  have hr : Nat.card R = 11520 := by
    rw [card_map_of_injective pairDesignEquiv.injective,native_card]
  obtain ⟨B₀,hB₀,hR⟩ := design_card11520_eq_hexad R hr
  obtain ⟨u,hu⟩ := exists_smul_m22Hexad123_eq hB₀
  obtain ⟨v,hv⟩ := exists_smul_m22Hexad123_eq hB
  let g : m22DesignAut := inclusion (v*u⁻¹)
  have hg : g • B₀ = B := by
    change (v*u⁻¹) • B₀ = B
    rw [mul_smul,←hu,inv_smul_smul,hv]
  exact ⟨(Outer.equivMapOfInjective pairDesignEquiv.toMonoidHom pairDesignEquiv.injective).trans
    ((MulEquiv.subgroupCongr hR).trans
      ((MulAction.stabilizerEquivStabilizer hg.symm).trans
        ((MulAction.stabilizer m22DesignAut B).equivMapOfInjective
          m22DesignAutToAut m22DesignAutToAut_injective)))⟩

noncomputable def nativeHexadEquiv (B : Finset (Fin 22)) (hB : B ∈ m22Blocks) :
    Outer ≃* designStabilizer B := (exists_native_hexad_equiv B hB).some

variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (P : PointData z)

/-- The actual point-plane overlap modulo the full cubic lift Q A. -/
abbrev Original := (P.M.subgroupOf (centralizer z)) ⧸
  (twoThreeCore (centralizer z)).subgroupOf (P.M.subgroupOf (centralizer z))

/-- The original cubic projection, followed by the constructed native hexad placement. -/
noncomputable def originalEquiv : Original P ≃* Outer :=
  (P.planeQuotientEquiv h).trans (nativeHexadEquiv P.hexad P.hexad_mem).symm

/-- The source quotient map is retained, before taking its two-core quotient. -/
theorem originalEquiv_marking (g : P.M.subgroupOf (centralizer z)) :
    nativeHexadEquiv P.hexad P.hexad_mem (originalEquiv h P (QuotientGroup.mk' _ g)) =
      overlapProjection P.cubic _ _ P.overlap g := by
  change nativeHexadEquiv P.hexad P.hexad_mem
    ((nativeHexadEquiv P.hexad P.hexad_mem).symm (P.planeQuotientEquiv h _)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

noncomputable def originalRadicalEquiv : pCore 2 (Original P) ≃* pCore 2 Outer :=
  ((pCore 2 (Original P)).equivMapOfInjective (originalEquiv h P).toMonoidHom
    (originalEquiv h P).injective).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 (originalEquiv h P)))

@[simp] theorem originalRadicalEquiv_coe (n : pCore 2 (Original P)) :
    (originalRadicalEquiv h P n).val = originalEquiv h P n.val := rfl

noncomputable def originalCoordinates : pCore 2 (Original P) ≃* Multiplicative V :=
  (originalRadicalEquiv h P).trans nativeCoordinates

noncomputable def originalActor : Original P →* Sp :=
  nativeActor.comp (originalEquiv h P).toMonoidHom

theorem originalActor_surjective : Function.Surjective (originalActor h P) :=
  nativeActor_surjective.comp (originalEquiv h P).surjective

theorem originalEquiv_mem_radical (x : Original P) :
    originalEquiv h P x ∈ pCore 2 Outer ↔ x ∈ pCore 2 (Original P) := by
  rw [←pCore_map_iso 2 (originalEquiv h P)]
  exact mem_map_iff_mem (f := (originalEquiv h P).toMonoidHom) (originalEquiv h P).injective

theorem originalActor_ker : (originalActor h P).ker = pCore 2 (Original P) := by
  ext x
  change nativeActor (originalEquiv h P x) = 1 ↔ _
  rw [←MonoidHom.mem_ker,nativeActor_ker]
  exact originalEquiv_mem_radical h P x

/-- Intrinsic kernel coordinates, rather than an independent module witness. -/
theorem originalCoordinates_conjugation (g : Original P) (n : pCore 2 (Original P)) :
    (originalCoordinates h P (MulAut.conjNormal g n)).toAdd =
      natural (originalActor h P g) (originalCoordinates h P n).toAdd := by
  have he : originalRadicalEquiv h P (MulAut.conjNormal g n) =
      MulAut.conjNormal (originalEquiv h P g) (originalRadicalEquiv h P n) := by
    apply Subtype.ext
    change originalEquiv h P (g*n.val*g⁻¹) =
      originalEquiv h P g * originalEquiv h P n.val * (originalEquiv h P g)⁻¹
    simp only [map_mul,map_inv]
  change (nativeCoordinates (originalRadicalEquiv h P (MulAut.conjNormal g n))).toAdd = _
  rw [he]
  exact nativeCoordinates_conjugation (originalEquiv h P g) (originalRadicalEquiv h P n)

theorem originalCoordinates_symm (v : V) :
    ((originalCoordinates h P).symm (Multiplicative.ofAdd v)).val =
      (originalEquiv h P).symm (nativeCoordinates.symm (Multiplicative.ofAdd v)).val := by
  apply (originalEquiv h P).injective
  rw [MulEquiv.apply_symm_apply]
  change (originalRadicalEquiv h P
    ((originalRadicalEquiv h P).symm (nativeCoordinates.symm (Multiplicative.ofAdd v)))).val = _
  rw [MulEquiv.apply_symm_apply]

/-- The quotient still uses the intrinsic radical of the original cubic-lift quotient. -/
noncomputable def originalQuotient :
    (Original P ⧸ pCore 2 (Original P)) ≃* Sp :=
  (QuotientGroup.congr _ _ (originalEquiv h P) (pCore_map_iso 2 (originalEquiv h P))).trans
    nativeQuotient

@[simp] theorem originalQuotient_mk (g : Original P) :
    originalQuotient h P (QuotientGroup.mk' _ g) = originalActor h P g := rfl

noncomputable def originalRepresentation :
    Representation (ZMod 2) (Original P ⧸ pCore 2 (Original P)) V :=
  natural.comp (originalQuotient h P).toMonoidHom

/-- The H1 calculation on the actual overlap quotient and its marked radical action. -/
theorem original_finrank_H1 :
    Module.finrank (ZMod 2) (H1 (originalRepresentation h P)) = 1 := by
  rw [(H1Congr (originalRepresentation h P) natural (originalQuotient h P)
    (LinearEquiv.refl (ZMod 2) V) (fun _ _ => rfl)).finrank_eq]
  exact full_finrank_H1

/-- Every automorphism fixing the original radical has just one quadratic
parameter after removing its principal displacement. -/
theorem original_automorphism_normal_form (α : MulAut (Original P))
    (hfix : ∀ n ∈ pCore 2 (Original P), α n = n) :
    ∃ (t : ZMod 2) (v : V), ∀ g : Original P,
      α g = ((originalCoordinates h P).symm (Multiplicative.ofAdd
        (t • quadraticCocycle.val (originalActor h P g) +
          (natural (originalActor h P g) v - v))) : Original P) * g := by
  let β := MulAut.congr (originalEquiv h P) α
  have hb : ∀ n ∈ pCore 2 Outer, β n = n := by
    intro n hn
    have hm : (originalEquiv h P).symm n ∈ pCore 2 (Original P) :=
      (originalEquiv_mem_radical h P _).mp (by rwa [MulEquiv.apply_symm_apply])
    change originalEquiv h P (α ((originalEquiv h P).symm n)) = n
    rw [hfix _ hm,MulEquiv.apply_symm_apply]
  obtain ⟨t,v,hv⟩ := native_automorphism_normal_form β hb
  refine ⟨t,v,fun g => ?_⟩
  apply (originalEquiv h P).injective
  rw [map_mul,originalCoordinates_symm,MulEquiv.apply_symm_apply]
  have he := hv (originalEquiv h P g)
  change originalEquiv h P (α ((originalEquiv h P).symm (originalEquiv h P g))) = _ at he
  rwa [MulEquiv.symm_apply_apply] at he

/-- A constructed correction on the original overlap's cubic-lift quotient. -/
noncomputable def originalQuadraticTwist : MulAut (Original P) :=
  MulAut.congr (originalEquiv h P).symm nativeQuadraticTwist

private theorem original_congr_inverse (α : MulAut (Original P)) :
    MulAut.congr (originalEquiv h P).symm (MulAut.congr (originalEquiv h P) α) = α := by
  apply MulEquiv.ext
  intro g
  change (originalEquiv h P).symm (originalEquiv h P
    (α ((originalEquiv h P).symm (originalEquiv h P g)))) = α g
  rw [MulEquiv.symm_apply_apply,MulEquiv.symm_apply_apply]

theorem originalQuadraticTwist_sq : originalQuadraticTwist h P ^ 2 = 1 := by
  change MulAut.congr (originalEquiv h P).symm nativeQuadraticTwist ^ 2 = 1
  rw [←map_pow,nativeQuadraticTwist_sq,map_one]

theorem originalQuadraticTwist_fixes_radical (n : pCore 2 (Original P)) :
    originalQuadraticTwist h P n.val = n.val := by
  change (originalEquiv h P).symm
    (nativeQuadraticTwist (originalEquiv h P n.val)) = n.val
  have he := nativeQuadraticTwist_fixes_radical (originalRadicalEquiv h P n)
  change nativeQuadraticTwist (originalEquiv h P n.val) = originalEquiv h P n.val at he
  rw [he,MulEquiv.symm_apply_apply]

theorem originalQuadraticTwist_not_inner :
    ¬ ∃ g : Original P, originalQuadraticTwist h P = MulAut.conj g := by
  rintro ⟨g,hg⟩
  apply nativeQuadraticTwist_not_inner
  refine ⟨originalEquiv h P g,?_⟩
  have he := congrArg (MulAut.congr (originalEquiv h P)) hg
  rw [MulAut.congr_conj] at he
  have ht : MulAut.congr (originalEquiv h P) (originalQuadraticTwist h P) =
      nativeQuadraticTwist := by
    apply MulEquiv.ext
    intro x
    change originalEquiv h P ((originalEquiv h P).symm
      (nativeQuadraticTwist (originalEquiv h P ((originalEquiv h P).symm x)))) = _
    rw [MulEquiv.apply_symm_apply,MulEquiv.apply_symm_apply]
  exact ht.symm.trans he

/-- Exactly the two possible outer classes for pointwise radical fixers in
I/(Q A), with an actual correcting element and an actual involutory twist. -/
theorem original_automorphism_factorization (α : MulAut (Original P))
    (hfix : ∀ n ∈ pCore 2 (Original P), α n = n) :
    ∃ n : pCore 2 (Original P), α = MulAut.conj n.val ∨
      α = MulAut.conj n.val * originalQuadraticTwist h P := by
  let β := MulAut.congr (originalEquiv h P) α
  have hb : ∀ n ∈ pCore 2 Outer, β n = n := by
    intro n hn
    have hm : (originalEquiv h P).symm n ∈ pCore 2 (Original P) :=
      (originalEquiv_mem_radical h P _).mp (by rwa [MulEquiv.apply_symm_apply])
    change originalEquiv h P (α ((originalEquiv h P).symm n)) = n
    rw [hfix _ hm,MulEquiv.apply_symm_apply]
  obtain ⟨n,hn⟩ := native_automorphism_factorization β hb
  let m := (originalRadicalEquiv h P).symm n
  have hm : (originalEquiv h P).symm n.val = m.val := by
    apply (originalEquiv h P).injective
    rw [MulEquiv.apply_symm_apply]
    exact (congrArg Subtype.val ((originalRadicalEquiv h P).apply_symm_apply n)).symm
  refine ⟨m,?_⟩
  rcases hn with hn | hn
  · left
    have he := congrArg (MulAut.congr (originalEquiv h P).symm) hn
    rw [original_congr_inverse h P,MulAut.congr_conj,hm] at he
    exact he
  · right
    have he := congrArg (MulAut.congr (originalEquiv h P).symm) hn
    rw [original_congr_inverse h P,map_mul,MulAut.congr_conj,hm] at he
    exact he

/-- The original cubic-lift quotient has precisely the constructed two
outer classes. No automorphism or module-classification premise is supplied. -/
theorem original_all_automorphisms (α : MulAut (Original P)) :
    ∃ x : Original P, α = MulAut.conj x ∨
      α = MulAut.conj x * originalQuadraticTwist h P := by
  obtain ⟨x,hx⟩ := native_all_automorphisms (MulAut.congr (originalEquiv h P) α)
  refine ⟨(originalEquiv h P).symm x,?_⟩
  rcases hx with hx | hx
  · left
    have he := congrArg (MulAut.congr (originalEquiv h P).symm) hx
    rw [original_congr_inverse h P,MulAut.congr_conj] at he
    exact he
  · right
    have he := congrArg (MulAut.congr (originalEquiv h P).symm) hx
    rw [original_congr_inverse h P,map_mul,MulAut.congr_conj] at he
    exact he

/-- For the SAME earlier cubic marking the denominator is literally Q A,
including its scalar cubic, not just Q or the marked central involution. -/
theorem original_denominator (a : SourceIncidence.LocalData h) :
    (twoThreeCore (centralizer z)).subgroupOf (a.P.M.subgroupOf (centralizer z)) =
      (core z ⊔ cubicSylowImage a.e a.X).subgroupOf
        (a.P.M.subgroupOf (centralizer z)) := by
  rw [core_sup_cubicSylow a.e h a.X,cubicLift_eq_twoThreeCore h a.e]

/-- All quotient clauses for the original overlap, with the same native
coordinates, quotient actor, and an explicitly constructed outer twist. -/
theorem original_comparison :
    Module.finrank (ZMod 2) (H1 (originalRepresentation h P)) = 1 ∧
    (originalActor h P).ker = pCore 2 (Original P) ∧
    (∀ g : Original P, ∀ n : pCore 2 (Original P),
      (originalCoordinates h P (MulAut.conjNormal g n)).toAdd =
        natural (originalActor h P g) (originalCoordinates h P n).toAdd) ∧
    originalQuadraticTwist h P ^ 2 = 1 ∧
    (¬ ∃ x : Original P, originalQuadraticTwist h P = MulAut.conj x) ∧
    (∀ n : pCore 2 (Original P), originalQuadraticTwist h P n.val = n.val) ∧
    (∀ α : MulAut (Original P), ∃ x : Original P,
      α = MulAut.conj x ∨ α = MulAut.conj x * originalQuadraticTwist h P) :=
  ⟨original_finrank_H1 h P,originalActor_ker h P,originalCoordinates_conjugation h P,
    originalQuadraticTwist_sq h P,originalQuadraticTwist_not_inner h P,
    originalQuadraticTwist_fixes_radical h P,original_all_automorphisms h P⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
