module
public import Theory.SpecificGroups.OddFourRank
public import Theory.Representation.DegreeFourFrattini
public import Theory.Frattini.SquareImage
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Elementary central quotients in determinant-one degree four

For a finite two-group faithfully represented in determinant-one degree four
in odd characteristic, every elementary central quotient has order at most 32.
A normal abelian self-centralizer has omega order at most eight. Its quotient
acts faithfully on at most four character weights and is elementary, hence
has order at most four. The Frattini subgroup comparison gives 32. Lifting
an elementary subgroup through a central quotient gives projective rank five.

Source application: the odd PSU₄ row in Aschbacher--Smith 4.4.3, printed
p.622, as used in 10.2.3(2), printed p.745.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement TensorProduct
namespace Representation.ProjectiveFour

private theorem symmetric_rank : primeRank 2 (Equiv.Perm (Fin 4)) ≤ 2 := by
  let P : Sylow 2 (Equiv.Perm (Fin 4)) := Classical.choice inferInstance
  obtain ⟨e⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  rw [P.primeRank_eq, primeRank_equiv 2 e]
  exact dihedral_rank_le_two 2

/-- An elementary central quotient of a determinant-one degree-four two-group has order at most 32. -/
theorem elementary_quotient_card_le_thirtyTwo
    {F P Q : Type*} [Field F] [Group P] [Finite P] [Group Q]
    [IsElementaryAbelian 2 Q]
    (hP : IsPGroup 2 P) (ρ : P →* GL (Fin 4) F)
    (hρ : Function.Injective ρ) (h2 : (2 : F) ≠ 0)
    (hdet : ∀ x, Matrix.GeneralLinearGroup.det (ρ x) = 1)
    (f : P →* Q) (hf : Function.Surjective f) (hc : f.ker ≤ center P) :
    Nat.card Q ≤ 32 := by
  classical
  obtain ⟨A,hAn,hAc,hCA⟩ := exists_normal_abelian_selfCentralizing hP
  let : A.Normal := hAn
  let : IsMulCommutative A := hAc
  let E := AlgebraicClosure F
  let σ₀ : Representation F P (Fin 4 → F) := (generalLinearNatural 4).comp ρ
  let σ := σ₀.extendScalars E
  have hσ : Function.Injective σ := (extendScalars_faithful_iff E σ₀).mp
    ((generalLinearNatural_injective 4).comp hρ)
  have h2E : (2 : E) ≠ 0 := by
    intro hh
    apply h2
    apply (algebraMap F E).injective
    simpa only [map_ofNat,map_zero] using hh
  have horder : (Nat.card A : E) ≠ 0 := by
    obtain ⟨k,hk⟩ := (hP.to_subgroup A).exists_card_eq
    rw [hk,Nat.cast_pow]
    exact pow_ne_zero _ h2E
  obtain ⟨j,hj⟩ := automizer_embeds_perm_of_abelian σ A hσ horder 4
    (by simp only [Module.finrank_baseChange,Module.finrank_pi,Fintype.card_fin,le_refl])
  let i : P →* normalizer (A : Set P) :=
    (MonoidHom.id P).codRestrict _ (fun g => by rw [A.normalizer_eq_top]; trivial)
  let g : P →* Equiv.Perm (Fin 4) :=
    j.comp (A.normalizerMonoidHom.rangeRestrict.comp i)
  have hgker : g.ker = A := by
    ext x
    change j (A.normalizerMonoidHom.rangeRestrict (i x)) = 1 ↔ x ∈ A
    rw [←j.map_one,hj.eq_iff]
    change A.normalizerMonoidHom.rangeRestrict (i x) = 1 ↔ x ∈ A
    rw [Subtype.ext_iff]
    change i x ∈ A.normalizerMonoidHom.ker ↔ x ∈ A
    rw [A.normalizerMonoidHom_ker]
    change x ∈ centralizer (A : Set P) ↔ x ∈ A
    exact ⟨fun h => hCA h, fun h => A.le_centralizer h⟩
  have hfg : f.ker ≤ g.ker := by
    rw [hgker]
    exact hc.trans ((center_le_centralizer (A : Set P)).trans hCA)
  have hpow (x : P) : g x ^ 2 = 1 := by
    rw [←map_pow]
    apply hfg
    rw [MonoidHom.mem_ker,map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 Q) _
  have hcomm (x y : P) : g x * g y = g y * g x := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply hfg
    rw [MonoidHom.mem_ker,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  let : IsElementaryAbelian 2 g.range := {
    toIsMulCommutative := ⟨⟨by
      rintro ⟨_,x,rfl⟩ ⟨_,y,rfl⟩
      exact Subtype.ext (hcomm x y)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      rintro ⟨_,x,rfl⟩
      exact Subtype.ext (hpow x)) }
  have hi : A.index ≤ 4 := by
    rw [←hgker,index_ker]
    exact (primeRank_le_iff_elementary_card_le _).mp symmetric_rank g.range inferInstance
  let O := omega₁ A (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative A
  have hO : Nat.card O ≤ 8 :=
    Theory.SpecificGroups.OddFourRank.elementary_card_le_eight
      ((ρ.comp A.subtype).comp O.subtype)
      ((hρ.comp A.subtype_injective).comp O.subtype_injective) h2
      (fun x => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 O) x)
      (fun x => hdet x.val.val)
  have hΦ : Nat.card (P ⧸ frattini P) ≤ 32 :=
    (hP.card_frattini_quotient_le_index_mul_omega_one A).trans (Nat.mul_le_mul hi hO)
  let q := QuotientGroup.lift (frattini P) f
    (frattini_le_ker_of_square_image f (fun x =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 Q) _))
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y,rfl⟩ := hf x
    exact ⟨QuotientGroup.mk' (frattini P) y,rfl⟩
  exact (Nat.card_le_card_of_surjective q hq).trans hΦ

/-- Central quotients of faithful determinant-one degree-four groups have two-rank at most five. -/
theorem central_quotient_twoRank_le_five
    {F G H : Type*} [Field F] [Group G] [Finite G] [Group H] [Finite H]
    (ρ : G →* GL (Fin 4) F) (hρ : Function.Injective ρ) (h2 : (2 : F) ≠ 0)
    (hdet : ∀ x, Matrix.GeneralLinearGroup.det (ρ x) = 1)
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G) :
    primeRank 2 H ≤ 5 := by
  apply (primeRank_le_iff_elementary_card_le H).mpr
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  let L := A.comap f
  let q : L →* A := f.subgroupComap A
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective A hf
  let P : Sylow 2 L := Sylow.nonempty.some
  have hPtop : (P : Subgroup L).map q = ⊤ := by
    change (P.mapSurjective hq : Subgroup A) = ⊤
    apply top_unique
    exact ((IsElementaryAbelian.isPGroup 2 A).to_subgroup ⊤).le_sylow_of_normal _
  let g : P →* A := q.comp (P : Subgroup L).subtype
  have hg : Function.Surjective g := by
    intro a
    have ha : a ∈ (P : Subgroup L).map q := hPtop.symm ▸ mem_top a
    obtain ⟨x,hx,he⟩ := ha
    exact ⟨⟨x,hx⟩,he⟩
  let j : P →* G := L.subtype.comp (P : Subgroup L).subtype
  have hj : Function.Injective j := L.subtype_injective.comp (P : Subgroup L).subtype_injective
  have hgc : g.ker ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply hj
    exact mem_center_iff.mp (hc (show j x ∈ f.ker from
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx))) (j y)
  exact elementary_quotient_card_le_thirtyTwo P.isPGroup' (ρ.comp j)
    (hρ.comp hj) h2 (fun x => hdet (j x)) g hg hgc
end Representation.ProjectiveFour
