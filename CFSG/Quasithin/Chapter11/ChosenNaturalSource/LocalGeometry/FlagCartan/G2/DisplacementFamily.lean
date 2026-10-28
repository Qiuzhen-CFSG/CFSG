module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PlaneOrbit

/-!
# Sylow displacement families and ambient conjugation

A plane above the first flag space is described by commutators landing in
that space. Conjugation transports these displacement subgroups with their
actual embedded Sylows. Sylow conjugacy then describes the entire plane
orbit from one marked plane. This is the group-theoretic transport used by
G2.SourceDisplacement and G2.DisplacementNormalizer; it does not identify
planes with ordinary fixed subgroups.

Source: the corrected G₂ geometric step in Aschbacher--Smith 11.1.4,
printed p.765, using the quotient fixed-plane description of I.2.3, p.413.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.Displacement
variable {G H : Type*} [Group G] [Group H]

/-- Displacement modulo W, restricted to A. The normalizer condition makes
this a subgroup without any unstated normality assumption on W. -/
def subgroup (A W B : Subgroup G) : Subgroup G where
  carrier := {v | v ∈ A ∧ v ∈ normalizer (W : Set G) ∧ ∀ p ∈ B, ⁅p,v⁆ ∈ W}
  one_mem' := by
    refine ⟨A.one_mem, (normalizer (W : Set G)).one_mem, ?_⟩
    intro p _
    rw [commutatorElement_one_right]
    exact W.one_mem
  mul_mem' := by
    rintro x y ⟨hx, hxN, hxD⟩ ⟨hy, hyN, hyD⟩
    refine ⟨A.mul_mem hx hy, (normalizer _).mul_mem hxN hyN, ?_⟩
    intro p hp
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hm := W.mul_mem (hxD p hp) ((hxN _).mp (hyD p hp))
    simpa only [mul_assoc] using hm
  inv_mem' := by
    rintro x ⟨hx, hxN, hxD⟩
    refine ⟨A.inv_mem hx, (normalizer _).inv_mem hxN, ?_⟩
    intro p hp
    rw [commutatorElement_inv_right, ← commutatorElement_inv]
    have hm : x⁻¹ * ⁅p,x⁆⁻¹ * x⁻¹⁻¹ ∈ W :=
      ((normalizer (W : Set G)).inv_mem hxN _).mp (W.inv_mem (hxD p hp))
    simpa only [inv_inv] using hm

theorem mem_subgroup {A W B : Subgroup G} (hA : A ≤ normalizer (W : Set G)) (v : G) :
    v ∈ subgroup A W B ↔ v ∈ A ∧ ∀ p ∈ B, p * v * p⁻¹ * v⁻¹ ∈ W := by
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, hA h.1, h.2⟩

theorem map_subgroup (e : G ≃* H) (A W B : Subgroup G) :
    (subgroup A W B).map e.toMonoidHom =
      subgroup (A.map e.toMonoidHom) (W.map e.toMonoidHom) (B.map e.toMonoidHom) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨mem_map_of_mem _ hv.1, ?_, ?_⟩
    · rw [← map_equiv_normalizer_eq]
      exact mem_map_of_mem _ hv.2.1
    · rintro _ ⟨p, hp, rfl⟩
      rw [← map_commutatorElement]
      exact mem_map_of_mem _ (hv.2.2 p hp)
  · intro v hv
    refine ⟨e.symm v, ⟨?_, ?_, ?_⟩, e.apply_symm_apply v⟩
    · exact (mem_map_equiv).mp hv.1
    · have hn := hv.2.1
      rw [← map_equiv_normalizer_eq] at hn
      exact (mem_map_equiv).mp hn
    · intro p hp
      have hd := hv.2.2 (e p) (mem_map_of_mem _ hp)
      have h := (mem_map_equiv).mp hd
      simpa only [map_commutatorElement, e.symm_apply_apply] using h

/-- Conjugation by a common normalizer permutes the actual Sylow displacement subgroups. -/
theorem normalizer_permutes [Finite G] {A W B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hW : g ∈ normalizer (W : Set G))
    (hB : g ∈ normalizer (B : Set G)) (P : Sylow 2 B) :
    ∃ Q : Sylow 2 B,
      (subgroup A W ((P : Subgroup B).map B.subtype)).map (MulAut.conj g).toMonoidHom =
        subgroup A W ((Q : Subgroup B).map B.subtype) := by
  let a := B.normalizerMonoidHom ⟨g, hB⟩
  refine ⟨P.mapSurjective (f := a.toMonoidHom)
    (show Function.Surjective a.toMonoidHom from a.surjective), ?_⟩
  have ha : A.map (MulAut.conj g).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp hA
  have hw : W.map (MulAut.conj g).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp hW
  rw [map_subgroup, ha, hw, Sylow.coe_mapSurjective, map_map, map_map]
  rfl

/-- Sylow conjugacy describes the full orbit from one displacement plane. -/
theorem orbit_eq_range [Finite G] {A W B U : Subgroup G}
    (hA : B ≤ normalizer (A : Set G)) (hW : B ≤ normalizer (W : Set G))
    (P : Sylow 2 B) (hP : U = subgroup A W ((P : Subgroup B).map B.subtype)) :
    Normalizers.planeOrbit U B = Set.range (fun Q : Sylow 2 B =>
      subgroup A W ((Q : Subgroup B).map B.subtype)) := by
  apply Set.ext
  intro Z
  constructor
  · rintro ⟨b, rfl⟩
    rw [hP]
    obtain ⟨Q,hQ⟩ := normalizer_permutes (hA b.property) (hW b.property)
      (B.le_normalizer b.property) P
    exact ⟨Q,hQ.symm⟩
  · rintro ⟨Q,rfl⟩
    obtain ⟨b,hb⟩ := MulAction.exists_smul_eq B P Q
    refine ⟨b, ?_⟩
    have ha : A.map (MulAut.conj (b : G)).toMonoidHom = A :=
      mem_normalizer_iff_map_conj_eq.mp (hA b.property)
    have hw : W.map (MulAut.conj (b : G)).toMonoidHom = W :=
      mem_normalizer_iff_map_conj_eq.mp (hW b.property)
    rw [hP, map_subgroup, ha, hw]
    dsimp only
    congr 1
    rw [← hb, Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.pointwise_smul_def, map_map, map_map]
    rfl

/-- Restriction to a larger ambient subgroup does not change a displacement subgroup it contains. -/
theorem restrict_eq {A C W B : Subgroup G} (hCA : C ≤ A)
    (hC : subgroup A W B ≤ C) : subgroup C W B = subgroup A W B := by
  ext v
  constructor
  · exact fun h => ⟨hCA h.1, h.2⟩
  · exact fun h => ⟨hC h, h.2⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.Displacement
