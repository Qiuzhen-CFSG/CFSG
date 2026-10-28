module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.CartanPlane
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# Simultaneous Sylow and Cartan-torsion coordinates

Conjugate the original inner Sylow to the standard unipotent subgroup.
An odd-primary subgroup in its Borel then fixes a coset of the diagonal
complement: its index is a power of two. Conjugating inside that Borel
aligns the odd subgroup while preserving the specified Sylow.

The two source applications use the original SL3 or Sp4 action marking
and the literal omega-core of the actual Hall subgroup. Only an inner
change of coordinates is made. CartanPlane supplies the required
placement; no marking of the outside component is imported.
The compatible outer action is developed by this parameter-component
owner, with final source assembly in qt-d-1222-shadow-linear-geometry.
Source: Aschbacher--Smith, 11.3.5(2), printed pp.771--772.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired

private theorem map_conj_twice {G : Type*} [Group G] (P : Subgroup G) (a b : G) :
    (P.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      P.map (MulAut.conj (b*a)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
  group

private theorem aligned_prime_subgroup {G : Type*} [Group G]
    (U B C S P : Subgroup G) (hB : normalizer (U : Set G) = B)
    (a : G) (ha : U.map (MulAut.conj a).toMonoidHom = S)
    (p : ℕ) [Fact p.Prime] (hP : IsPGroup p P)
    (hPN : P ≤ normalizer (S : Set G)) (hi : ¬ p ∣ (C.subgroupOf B).index) :
    ∃ b : G, S.map (MulAut.conj b).toMonoidHom = U ∧
      P.map (MulAut.conj b).toMonoidHom ≤ C := by
  let P' := P.map (MulAut.conj a⁻¹).toMonoidHom
  have hSU : S.map (MulAut.conj a⁻¹).toMonoidHom = U := by
    rw [←ha,map_conj_twice]
    simp only [inv_mul_cancel]
    have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [he,map_id]
  have hP' : P' ≤ B := by
    rw [←hB,←hSU,←map_equiv_normalizer_eq S (MulAut.conj a⁻¹)]
    exact map_mono hPN
  obtain ⟨u,hu⟩ := exists_conj_overgroup_of_index_primeTo
    (P'.subgroupOf B) (C.subgroupOf B) (hP.map _ |>.comap_subtype) hi
  refine ⟨(u : G)*a⁻¹,?_,?_⟩
  · rw [←map_conj_twice,hSU]
    exact mem_normalizer_iff_map_conj_eq.mp (hB.symm ▸ u.property)
  · rw [←map_conj_twice]
    rintro _ ⟨x,hx,rfl⟩
    exact hu (show (⟨x,hP' hx⟩ : B) ∈ P'.subgroupOf B from hx)

namespace SL3
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.CartanActions.BorelQuotient
variable {F : Type*} [Field F] [Finite F]

/-- Simultaneously align the specified Sylow and an odd-primary subgroup
of its normalizer, retaining an actual conjugator in the full SL3 group. -/
theorem align_prime_subgroup {n p : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hp2 : p ≠ 2)
    (S : Sylow 2 SL(3,F)) (P : Subgroup SL(3,F)) (hP : IsPGroup p P)
    (hPN : P ≤ normalizer (S : Set SL(3,F))) :
    ∃ b : SL(3,F), (S : Subgroup SL(3,F)).map (MulAut.conj b).toMonoidHom = unipotentSL F ∧
      P.map (MulAut.conj b).toMonoidHom ≤ (torusSL F).range := by
  obtain ⟨a,ha,_⟩ := sylowSL_normalizer_conjugate F hn hF S
  apply aligned_prime_subgroup (unipotentSL F) (borelSL F) (torusSL F).range S P
    (normalizer_unipotentSL F) a ha p hP hPN
  rw [(borelSL_complement F).index_eq_card,
    Nat.card_congr (subgroupOfEquivOfLe (unipotentSL_le_borelSL F)).toEquiv,
    card_unipotentSL,hF]
  intro hd
  have hp : p.Prime := Fact.out
  have hd2 := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd)
  exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one)

end SL3

namespace Sp4
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
private theorem torus_complement :
    (borelCharacters (F := F)).ker.IsComplement' (torusSection (F := F)).range := by
  refine ⟨mul_injective_of_disjoint ?_,?_⟩
  · apply disjoint_def.mpr
    rintro x hx ⟨y,rfl⟩
    have hy : y = 1 := (characters_torusSection y).symm.trans hx
    simp [hy]
  · intro x
    let y := torusSection (borelCharacters x)
    have hk : x*y⁻¹ ∈ (borelCharacters (F := F)).ker := by
      simp [y,MonoidHom.mem_ker]
    exact ⟨(⟨x*y⁻¹,hk⟩,⟨y,⟨borelCharacters x,rfl⟩⟩),by simp⟩

/-- The symplectic marking aligns the same specified Sylow and odd-primary
subgroup with the original unipotent and diagonal matrices. -/
theorem align_prime_subgroup {n p : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hp2 : p ≠ 2)
    (S : Sylow 2 (Sp F)) (P : Subgroup (Sp F)) (hP : IsPGroup p P)
    (hPN : P ≤ normalizer (S : Set (Sp F))) :
    ∃ b : Sp F, (S : Subgroup (Sp F)).map (MulAut.conj b).toMonoidHom = unipotent ∧
      P.map (MulAut.conj b).toMonoidHom ≤
        (CentralRootGeometry.diagonalTorusHom (F := F)).range := by
  obtain ⟨a,ha,_⟩ := sylow_normalizer_conjugate hF hn S
  let C : Subgroup (Sp F) := (torusSection (F := F)).range.map borel.subtype
  have hC : C.subgroupOf borel = (torusSection (F := F)).range :=
    comap_map_eq_self_of_injective borel.subtype_injective _
  have hind : ¬ p ∣ (C.subgroupOf borel).index := by
    rw [hC,torus_complement.index_eq_card,characters_ker,
      Nat.card_congr (subgroupOfEquivOfLe (show (unipotent : Subgroup (Sp F)) ≤ (borel (F := F)) from
        unipotent_le_borel)).toEquiv,card_unipotent,hF]
    intro hd
    have hp : p.Prime := Fact.out
    have hd2 := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow hd)
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one)
  obtain ⟨b,hb,hPb⟩ := aligned_prime_subgroup unipotent borel C S P
    borel_eq_normalizer_unipotent.symm a ha p hP hPN hind
  refine ⟨b,hb,hPb.trans ?_⟩
  rintro _ ⟨x,⟨d,rfl⟩,rfl⟩
  exact ⟨(d.1,d.1⁻¹*d.2),rfl⟩

end Sp4

open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

private theorem model_prime_subgroup_normalizes (c : Coordinates D S.field)
    (Q : Subgroup G) (hQ : Q ≤ cartanNormalizer T L) :
    (Q.subgroupOf L).map c.quotientMap ≤ normalizer (c.modelSylow : Set c.ModelGroup) := by
  rintro _ ⟨l,hl,rfl⟩
  have hh := (c.cartanProjection ⟨l,hQ hl⟩).property
  rwa [c.cartanProjection_coe] at hh

/-- The same original SL3 marking simultaneously sends the inner Sylow to
its unipotent model and every element of the literal Hall p-torsion to a
diagonal matrix. Only an inner change of coordinates is made. -/
theorem source_primeTorsion_alignment_sl3
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (A : Subgroup G) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : primeTorsion A p ≤ cartanNormalizer T L) :
    ∃ b : SL(3,S.field.Carrier),
      ((T : Subgroup G).subgroupOf L).map
        ((MulAut.conj b).toMonoidHom.comp (Coordinates.sl3 m).quotientMap) =
          Matrix.PSL3.LinearThree.unipotentSL S.field.Carrier ∧
      ∀ x : L, (x : G) ∈ primeTorsion A p →
        ∃ d : Fin 3 → S.field.Carrier,
          (b * (show SL(3,S.field.Carrier) from (Coordinates.sl3 m).quotientMap x) * b⁻¹).val = Matrix.diagonal d := by
  let c : Coordinates D S.field := .sl3 m
  let P := ((primeTorsion A p).subgroupOf L).map c.quotientMap
  have hP : IsPGroup p P := (primeTorsion_isPGroup A p).comap_subtype.map _
  obtain ⟨b,hb,hPb⟩ := SL3.align_prime_subgroup S.field.degree_pos S.field.card_eq hp2
    c.modelSylow P hP (model_prime_subgroup_normalizes c (primeTorsion A p) hQ)
  refine ⟨b,?_,?_⟩
  · rw [←map_map,←c.innerSylow_coe]
    exact hb
  · intro x hx
    have hh := hPb (mem_map_of_mem _ (mem_map_of_mem c.quotientMap hx))
    obtain ⟨d,hd⟩ := hh
    refine ⟨![d.1,((d.1*d.2)⁻¹ : S.field.Carrierˣ),d.2],?_⟩
    change (MulAut.conj b (c.quotientMap x)).val = _
    exact (congrArg (fun z : SL(3,S.field.Carrier) => z.val) hd.symm).trans
      (Matrix.PSL3.CartanActions.torusSL_val S.field.Carrier d)

/-- The corresponding symplectic alignment preserves the original quotient
and puts the same odd p-torsion in its full diagonal torus. -/
theorem source_primeTorsion_alignment_sp4
    (m : ActionEquiv D.centralQuotientAction (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (A : Subgroup G) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hQ : primeTorsion A p ≤ cartanNormalizer T L) :
    ∃ b : Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier,
      ((T : Subgroup G).subgroupOf L).map
        ((MulAut.conj b).toMonoidHom.comp (Coordinates.sp4 m).quotientMap) =
          Theory.SpecificGroups.SymplecticFour.unipotent ∧
      ((primeTorsion A p).subgroupOf L).map
        ((MulAut.conj b).toMonoidHom.comp (Coordinates.sp4 m).quotientMap) ≤
          (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.diagonalTorusHom
            (F := S.field.Carrier)).range := by
  let c : Coordinates D S.field := .sp4 m
  let P := ((primeTorsion A p).subgroupOf L).map c.quotientMap
  have hP : IsPGroup p P := (primeTorsion_isPGroup A p).comap_subtype.map _
  obtain ⟨b,hb,hPb⟩ := Sp4.align_prime_subgroup S.field.degree_pos S.field.card_eq hp2
    c.modelSylow P hP (model_prime_subgroup_normalizes c (primeTorsion A p) hQ)
  refine ⟨b,?_,?_⟩
  · rw [←map_map,←c.innerSylow_coe]
    exact hb
  · rw [←map_map]
    exact hPb

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Paired
