module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.LocalGeometry
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicRecognition

/-!
# The G₂ recognition step after construction of a local two-core

For the literal intersection J = (M ∩ L)* inside L*, a nontrivial O₂(J)
places J inside a root parabolic. The model theorem aligns the given component
Sylow with the standard positive roots. Conjugation by S* preserves this
Sylow, so it fixes both root parabolics. Each is proper because L* has trivial
two-core, inherited from I*. The source maximality of J among proper invariant
overgroups now gives equality with the containing parabolic.

The derived result includes both diagram labels. The binary specialization
uses the existing G₂(2)′ marking; the full-model specialization transports
through the component's actual perfectness and returns a full root parabolic.
There is no identification of the full binary group with its derived group.

Nontriviality of O₂(J) is an explicit premise in these three recognition
results. `G2Recognition.Source` discharges it using `G2TwoCore` for the full
and binary derived carriers, from the source residual, S₃ shadow and model facts.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.26–28,
printed pp.1130–1131 (PDF pp.1147–1148).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.G2Recognition
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.SylowParabolicRecognition
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

private theorem component_twoCore (a : Input d I c) :
    pCore 2 (d.starImage I c.L) = ⊥ := by
  let L := d.starImage I c.L
  let := a.componentStar_normal
  let R := (pCore 2 L).map L.subtype
  have hn : R.Normal := normalizer_eq_top_iff.mp (by
    apply top_unique
    have h := normalizer_le_normalizer_characteristic_image L (pCore 2 L)
    simpa only [normalizer_eq_top] using h)
  have hle : R ≤ pCore 2 (d.Star I) := le_sSup ⟨hn, pCore_isPGroup.map L.subtype⟩
  have hbot : R = ⊥ := bot_unique (hle.trans_eq
    (d.star_twoCore_eq_bot ⟨a.sylow, a.sylow_eq⟩ (d.Z_le_S a.module_le)))
  exact ((pCore 2 L).map_eq_bot_iff_of_injective L.subtype_injective).mp hbot

private theorem map_conjNormal_subgroupOf {A : Type*} [Group A] [Finite A]
    (L P : Subgroup A) [L.Normal] (s : A) (hs : s ∈ normalizer (P : Set A)) :
    (P.subgroupOf L).map (MulAut.conjNormal (H := L) s).toMonoidHom = P.subgroupOf L := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact (hs (x : A)).mp hx
  · rw [card_map_of_injective (f := (MulAut.conjNormal (H := L) s).toMonoidHom)
      (MulAut.conjNormal (H := L) s).injective]

/-- Recognition and both diagram labels from a nontrivial intrinsic two-core
of the literal component intersection. The core premise remains to be discharged. -/
theorem derived_marking_of_twoCore (a : Input d I c)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : d.starImage I c.L ≃* commutator (Model F))
    (hcore : pCore 2 ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) ≠ ⊥) :
    Nonempty (RankTwoParabolicMarking d I c.L (commutator (Model F))
      (rootParabolic (F := F))) := by
  let L := d.starImage I c.L
  let S := d.starImage I d.S
  let P := d.starImage I (d.M ⊓ c.L)
  let J := P.subgroupOf L
  let D := commutator (Model F)
  have hPL : P ≤ L := a.componentIntersectionStar_lt.le
  have hSM : S ≤ d.starImage I (d.MI I) :=
    map_mono (comap_mono (le_inf (inf_le_left.trans d.sylow_le) a.sylow_le))
  have hSP : S ⊓ L ≤ P := by
    rw [show P = L ⊓ d.starImage I (d.MI I) from a.intersectionStar_eq_inf]
    exact le_inf inf_le_right (inf_le_left.trans hSM)
  obtain ⟨Q, hQ⟩ := a.exists_componentSylow
  have hQJ : (Q : Subgroup L) ≤ J := by
    rw [hQ]
    exact fun x hx => hSP ⟨hx, x.property⟩
  obtain ⟨f, i, hQf, hJP⟩ := exists_aligned_parabolic_of_twoCore e Q J hQJ hcore
  have hDcore : pCore 2 D = ⊥ := by
    rw [← pCore_map_iso 2 e, component_twoCore a, Subgroup.map_bot]
  let := a.componentStar_normal
  have fixed (s : d.Star I) (hs : s ∈ S) (j : Fin 2) :
      (modelSubgroup d I c.L f (rootParabolic j)).map (MulAut.conj s).toMonoidHom =
        modelSubgroup d I c.L f (rootParabolic j) := by
    let b := MulAut.conjNormal (H := L) s
    let β : MulAut D := (f.symm.trans b).trans f
    have transport (K : Subgroup L) :
        (K.map f.toMonoidHom).map β.toMonoidHom =
          (K.map b.toMonoidHom).map f.toMonoidHom := by
      rw [map_map, map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f (b (f.symm (f x))) = f (b x)
      rw [f.symm_apply_apply]
    have hQb : (Q : Subgroup L).map b.toMonoidHom = Q := by
      rw [hQ]
      exact map_conjNormal_subgroupOf L S s (S.le_normalizer hs)
    have hU : (unipotent.subgroupOf D).map β.toMonoidHom = unipotent.subgroupOf D := by
      rw [← hQf, transport, hQb]
    have hPi := rootParabolic_invariant β hU j
    let m : D →* d.Star I := L.subtype.comp f.symm.toMonoidHom
    have hcomp : m.comp β.toMonoidHom = (MulAut.conj s).toMonoidHom.comp m := by
      ext x
      change ((f.symm (f (b (f.symm x))) : L) : d.Star I) =
        s * ((f.symm x : L) : d.Star I) * s⁻¹
      rw [f.symm_apply_apply]
      rfl
    change ((rootParabolic j).map m).map (MulAut.conj s).toMonoidHom =
      (rootParabolic j).map m
    rw [map_map, ← hcomp, ← map_map, hPi]
  let K := modelSubgroup d I c.L f (rootParabolic i)
  have hKmap : K.subgroupOf L = (rootParabolic i).map f.symm.toMonoidHom := by
    change (((rootParabolic i).map (L.subtype.comp f.symm.toMonoidHom)).comap L.subtype) = _
    rw [← map_map, comap_map_eq_self_of_injective L.subtype_injective]
  have hKL : K ≤ L := by
    change (rootParabolic i).map (L.subtype.comp f.symm.toMonoidHom) ≤ L
    rw [← map_map]
    exact map_subtype_le _
  have hPK : P ≤ K := by
    intro x hx
    have hm := hJP (mem_map_of_mem f.toMonoidHom
      (show (⟨x, hPL hx⟩ : L) ∈ J from hx))
    exact ⟨f ⟨x, hPL hx⟩, hm, by simp⟩
  have hKne : K ≠ L := by
    intro he
    have ht : (rootParabolic (F := F) i).map f.symm.toMonoidHom = ⊤ := by
      rw [← hKmap, he, subgroupOf_self]
    exact rootParabolic_ne_top hDcore i
      (f.symm.mapSubgroup.injective (ht.trans f.symm.mapSubgroup.map_top.symm))
  have hKP : K ≤ P := a.invariant_component_overgroup_le K hKL hKne
    ((map_mono (comap_mono (le_inf (a.yplus_le_intersection.trans inf_le_left)
      a.contains))).trans hPK) (hSP.trans hPK)
    (fun s hs => mem_normalizer_iff_map_conj_eq.mpr (fixed s hs i))
  have he : K = P := le_antisymm hKP hPK
  have hmark : J.map f.toMonoidHom = rootParabolic i := by
    apply (map_injective (f := f.symm.toMonoidHom) f.symm.injective)
    rw [map_map]
    have hm : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id L := by
      apply MonoidHom.ext
      intro x
      exact f.symm_apply_apply x
    rw [hm, map_id, ← hKmap, he]
  refine ⟨{ equiv := f, node := i, intersection := hmark, diagram := ?_ }⟩
  intro s hs j
  refine ⟨1, ?_⟩
  simp only [map_one, Subgroup.coe_one]
  change (modelSubgroup d I c.L f (rootParabolic j)).map (MulAut.conj s).toMonoidHom =
    (modelSubgroup d I c.L f (rootParabolic j)).map (MonoidHom.id _)
  rw [Subgroup.map_id]
  exact fixed s hs j

/-- Binary specialization keeps the proper commutator carrier and the existing
root-parabolic labels used by the source alternative. -/
theorem binary_marking_of_twoCore (a : Input d I c)
    (e : d.starImage I c.L ≃* commutator (Model (ZMod 2)))
    (hcore : pCore 2 ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) ≠ ⊥) :
    Nonempty (RankTwoParabolicMarking d I c.L (commutator (Model (ZMod 2)))
      g2DerivedParabolic) :=
  derived_marking_of_twoCore a e hcore

/-- For a full G₂ model perfectness comes from the actual component. The
conclusion identifies its intersection with a full root parabolic, without
silently replacing the full binary group by its derived subgroup. -/
theorem full_recognition_of_twoCore (a : Input d I c) (F : ClassificationField)
    (e : d.starImage I c.L ≃* Model F.Carrier)
    (hcore : pCore 2 ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) ≠ ⊥) :
    ∃ (f : d.starImage I c.L ≃* Model F.Carrier) (i : Fin 2),
      ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)).map f.toMonoidHom =
        (if i = 0 then parabolic₁ else parabolic₂) := by
  let := c.star_quasisimple
  let : Group.IsPerfect (Model F.Carrier) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have ht : commutator (Model F.Carrier) = ⊤ := Group.IsPerfect.commutator_eq_top
  let t : commutator (Model F.Carrier) ≃* Model F.Carrier :=
    (MulEquiv.subgroupCongr ht).trans topEquiv
  obtain ⟨m⟩ := derived_marking_of_twoCore a (e.trans t.symm) hcore
  refine ⟨m.equiv.trans t, m.node, ?_⟩
  change ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)).map
    (t.toMonoidHom.comp m.equiv.toMonoidHom) = _
  rw [← map_map, m.intersection]
  change ((if m.node = 0 then parabolic₁ else parabolic₂).subgroupOf
    (commutator (Model F.Carrier))).map (commutator (Model F.Carrier)).subtype = _
  exact map_subgroupOf_eq_of_le (le_top.trans ht.ge)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve.G2Recognition
