module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMoverLarge
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.LargeQuadratic

/-!
# No invariant refinement for the original small-mover join

Keep an arbitrary marking of the full vertex quotient and its exact natural
indices. A containing Sylow transports the small-mover family into the
standard coordinates. Its proved lower bound gives a large quadratic
maximum, which excludes a refinement by the orthogonal 2q bound. Conjugating
back retains the supplied marking for the full X-quotient consumer.
Source: MS93 (5.3), printed p.915, using (5.1) and (5.4).
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The small-mover join preserves no refinement under any compatible
whole-vertex natural marking, at the original nonbinary field degree. -/
theorem Input.replacement_small_mover_no_refinement
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (E : BinaryField) (hE : E.degree = n)
    (f : stabilizer d.radical a →* Sp E.Carrier) (_hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := E.Carrier) 2)) (A.map f)) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2)
    ¬ ∃ c : Vector E.Carrier, ∀ x : (J.subgroupOf (stabilizer d.radical a)).map f,
      ∀ v, refinement c (x.val • v)=refinement c v := by
  dsimp only
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  have hpT : IsPGroup 2 (Q d.radical t) := hjR ▸ (h.replacement_two_group d).map j
  obtain ⟨P,hP⟩ := (hpT.comap_subtype.map f).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp E.Carrier) P
    (unipotentSylow (by rw [E.card_eq]) (by rw [hE]; exact h.nonbinary.le))
  have hPm : (P : Subgroup (Sp E.Carrier)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun P : Sylow 2 (Sp E.Carrier) => (P : Subgroup (Sp E.Carrier))) hg
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hTf : T.map f' ≤ unipotent := by
    rw [←Subgroup.map_map]
    exact (map_mono hP).trans_eq hPm
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x) = 1 ↔ f x = 1
    exact (MulAut.conj g).map_eq_one_iff
  have hTi : T.map f' ≤ unipotent.subtype.range := by simpa only [range_subtype] using hTf
  have hidx (A : Subgroup S) (hAT : A ≤ T) :
      (centralizer (A : Set S)).relIndex U₀ =
        movingIndex (Degree.Quotient.coordinates f' unipotent.subtype A) := by
    have hAf := (map_mono hAT).trans hTf
    let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
    have hi : (centralizer (A : Set S)).relIndex U₀ = 2 ^ fixedCodim τ (A.map f') := by
      rw [←Subgroup.map_map,fixedCodim_map_conj]
      exact hindex A
    rw [hi,←binary_movingIndex]
    congr 1
    have hcomp : restrictScalars (k := ZMod 2) (natural (F := E.Carrier)) =
        τ.comp (unipotent (F := E.Carrier)).subtype := rfl
    rw [hcomp]
    rw [fixedCodim,fixedCodim,fixedSpace_comp_map,
      Degree.Quotient.coordinates_map f' unipotent.subtype A
        (by simpa only [range_subtype] using hAf)]
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let J := Subgroup.SmallMover.join U₀ f'.ker T (Nat.card E.Carrier ^ 2)
  have hJmap : J.map S.subtype = Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2) := by
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,hker,hfQ,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS,hcard]
  have hJsub : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F ^ 2)).subgroupOf S = J := by
    rw [←hJmap]
    exact comap_map_eq_self_of_injective S.subtype_injective _
  have hcoord := Degree.Quotient.coordinates_join U₀ T f' unipotent.subtype
    Subtype.val_injective (hker ▸ hkT) (hker ▸ hUK) hTi hidx
  have hJTi : J.map f' ≤ unipotent.subtype.range :=
    (map_mono (Subgroup.SmallMover.join_le _ _ _ _)).trans hTi
  have hJcoord := Degree.Quotient.coordinates_map f' unipotent.subtype J hJTi
  have hlarge : Nat.card E.Carrier^2 ≤
      Nat.card (Degree.join (Degree.Quotient.coordinates f' unipotent.subtype T)) := by
    have hc : Nat.card (Degree.join (Degree.Quotient.coordinates f' unipotent.subtype T)) =
        f'.ker.relIndex J := by
      rw [←hcoord,relIndex_ker,←hJcoord,card_map_of_injective Subtype.val_injective]
    rw [hc]
    have he := relIndex_map_map_of_injective f'.ker J S.subtype_injective
    rw [hker,hfQ,hJmap] at he
    rw [hker,←he,hcard]
    exact h.replacement_small_mover_join_index d geometry hb ha hat
  have hF : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hno := Degree.join_no_refinement hF _ hlarge
  rw [←hcoord,hJcoord] at hno
  rw [hJsub]
  rintro ⟨c,hc⟩
  obtain ⟨c',hc'⟩ := refinement_comp_symplectic c g⁻¹
  apply hno
  refine ⟨c',?_⟩
  rintro ⟨_,⟨x,hx,rfl⟩⟩ v
  rw [←hc',←hc']
  change refinement c (g⁻¹ • ((g*f x*g⁻¹) • v)) = refinement c (g⁻¹ • v)
  simp only [mul_smul,inv_smul_smul]
  exact hc ⟨f x,mem_map_of_mem f hx⟩ _

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
