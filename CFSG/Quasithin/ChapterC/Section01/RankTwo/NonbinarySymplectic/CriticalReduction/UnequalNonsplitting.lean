module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CrossFixedPaths

/-!
# The nonsplitting exception for unequal neighboring movers

When both movers contain the original vertex kernel Q, their central
omegas are exactly their fixed subgroups in the whole X-layer. The common
edge stabilizer conjugates the movers, so these fixed subgroups have equal
orders. A decomposition X = U C_X(G_alpha) would give equal fixed indices
on U. The established square index for the original mover and cubic index
for its unequal neighbor contradict that equality.

The actual root-selected-neighbor application discharges kernel containment
from the small-image saturation branch. It retains the same conjugator,
whole edge-Z fixed subgroup, B-relative U-index, quadratic own-layer actions,
and every overlap of the backward path or the trapped-root alternative.
All quotient kernels and central attachments remain present.

This proves the genuine nonsplitting clause in MS93 (5.5)(c), printed
pp.915--917, for the saturated branch. Individual generation, contained
large-image smaller-J selection, trapped-root and terminal exclusions,
and the minimum-replacement distance-two witness remain to be proved.
No original-radical characteristic preservation is inferred.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

private theorem fixed_index_of_split {G : Type*} [Group G]
    (X U C E : Subgroup G) [IsMulCommutative X]
    (hUX : U ≤ X) (hsplit : X = U ⊔ C)
    (hCE : C ≤ centralizer (E : Set G)) :
    (centralizer (E : Set G)).relIndex X =
      (centralizer (E : Set G)).relIndex U := by
  let Y := X ⊓ centralizer (E : Set G)
  have hCX : C ≤ X := le_sup_right.trans_eq hsplit.symm
  have hjoin : U ⊔ Y = X := by
    apply le_antisymm (sup_le hUX inf_le_left)
    exact hsplit.le.trans (sup_le le_sup_left
      ((show C ≤ Y from le_inf hCX hCE).trans le_sup_right))
  let : CommGroup X := IsMulCommutative.instCommGroup
  have hh := relIndex_sup_right (U.subgroupOf X) (Y.subgroupOf X)
  rw [←subgroupOf_sup hUX (show Y ≤ X from inf_le_left),hjoin,
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf hUX] at hh
  have he (V : Subgroup G) (hv : V ≤ X) :
      Y.subgroupOf V = (centralizer (E : Set G)).subgroupOf V := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨hv x.property,hx⟩⟩
  change (Y.subgroupOf X).index = (Y.subgroupOf U).index at hh
  rwa [he X le_rfl,he U hUX] at hh

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Unequal neighboring movers containing the original full kernel force
nonsplitting of the whole central omega layer over its ambient-fixed subgroup.
The latter is literally X intersect Z(G_alpha), since X lies in G_alpha. -/
theorem Input.replacement_unequal_kernel_nonsplitting
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (hQE : Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)) :
    X d.radical a ≠ U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  let W := X d.radical a
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hES : E ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hZX : Z d.radical a ≤ W := geometry.omega_bound a ha (by
    rw [geometry.distance_constant a ha]
    change 0 < geometry.b d.radical
    omega)
  have hZQ := hZX.trans (omegaCenter_le (Q d.radical a))
  have hC : C d.radical a = Q d.radical a := MSCentralOrbit.C_eq_Q _
    (h.replacement_two_group d) (h.replacement_core_le d)
    (h.replacement_omegaOrbit_centralizer d) a ha
  have homega (D : Subgroup (FreeAmalgam d.radical)) (hDS : D ≤ S)
      (hQD : Q d.radical a ≤ D) :
      omegaCenter D = W ⊓ centralizer (D : Set (FreeAmalgam d.radical)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxD,hx2,hxc⟩ := mem_omegaCenter_iff.mp hx
      have hxQ : x ∈ Q d.radical a := hC ▸
        (show x ∈ C d.radical a from ⟨hDS hxD,fun y hy => hxc y (hQD (hZQ hy))⟩)
      exact ⟨mem_omegaCenter_iff.mpr ⟨hxQ,hx2,fun y hy => hxc y (hQD hy)⟩,hxc⟩
    · rintro ⟨hx,hxc⟩
      obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp hx
      exact mem_omegaCenter_iff.mpr ⟨hQD hxQ,hx2,hxc⟩
  have hcard : Nat.card (omegaCenter J) = Nat.card (omegaCenter E) := by
    obtain ⟨g,hg,hga⟩ := stabilizer_transitive_neighbors d.radical t
      (adjacent_symm d.radical hat) (adjacent_symm d.radical hct)
    have hgt : act d.radical g t = t := hg
    have he : E = J.map (MulAut.conj g⁻¹).toMonoidHom := by
      dsimp only [E,J]
      conv_lhs => rw [←hga,←hgt]
      rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]
    rw [he,omegaCenter_map _ _ (MulAut.conj g⁻¹).injective,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
  rw [homega J hJS hQJ,homega E hES hQE] at hcard
  let := finite_X d.radical a
  let : Finite (W ⊓ centralizer (E : Set (FreeAmalgam d.radical)) : Subgroup _) :=
    Finite.of_injective (inclusion (show W ⊓ centralizer (E : Set _) ≤ W from inf_le_left))
      (inclusion_injective _)
  have hindex : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex W =
      (centralizer (E : Set (FreeAmalgam d.radical))).relIndex W := by
    have hJcard := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical))
      (W ⊓ centralizer (J : Set (FreeAmalgam d.radical))) W bot_le inf_le_left
    have hEcard := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical))
      (W ⊓ centralizer (E : Set (FreeAmalgam d.radical))) W bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at hJcard hEcard
    rw [hcard] at hJcard
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hJcard.trans hEcard.symm)
  intro hsplit
  let := X_elementary d.radical a
  have hUX := (U_le_Z a).trans hZX
  rw [fixed_index_of_split W (U d.radical a) _ J hUX hsplit
    (inf_le_right.trans (centralizer_le hJS)),
    fixed_index_of_split W (U d.radical a) _ E hUX hsplit
      (inf_le_right.trans (centralizer_le hES))] at hindex
  rw [(h.replacement_unequal_original_quadratic d geometry hb ha hat hct hne).1,
    (h.replacement_unequal_individual_edge_fixed d geometry hb ha hat hct hne).1] at hindex
  have hq : 1 < Nat.card F := Finite.one_lt_card
  nlinarith [show 0 < Nat.card F^2 from pow_pos Nat.card_pos 2]

/-- The same actual root-selected neighbor carries the source nonsplitting
clause in its small-image alternative, with every previously established
fixed-layer, quotient-kernel and path conclusion retained. Generation is still
by the join of both movers; no individual-generation assertion is added. -/
theorem Input.replacement_unequal_nonsplitting_root_at_neighbor
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    ∃ g ∈ Ltilde d.radical a,
      let w := act d.radical g⁻¹ t
      let v := act d.radical g⁻¹ c
      let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
          (Q d.radical t) (Nat.card F^2)
      let Ja := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w) (Nat.card F^2)
      let Ec := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical w) (Nat.card F^2)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      J.map (MulAut.conj g).toMonoidHom =
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical w) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
      J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      Z d.radical t ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅U d.radical a,Ja⁆,Ja⁆ = ⊥ ∧ ⁅⁅U d.radical v,Ec⁆,Ec⁆ = ⊥ ∧
      (centralizer (Ec : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F^3 ∧
      ((Nat.card F^2 < (Q d.radical a).relIndex Ec) ∨
        (Q d.radical a ≤ Ja ⊓ Ec ∧
          (Q d.radical a).relIndex Ja = Nat.card F^2 ∧
          (Q d.radical a).relIndex Ec = Nat.card F^2 ∧
          (Q d.radical a).relIndex (Ja ⊓ Ec) ≤ Nat.card F^2 ∧
          X d.radical a ≠ U d.radical a ⊔
            (X d.radical a ⊓ centralizer
              (stabilizer d.radical a : Set (FreeAmalgam d.radical))))) ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
      (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
        (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
        (Q d.radical a).relIndex (Z d.radical z) = Nat.card F ∧
        Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
          (Z d.radical z ⊓ Q d.radical a) ∧
        X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
        ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥)) := by
  obtain ⟨g,hg,haw,hvw,hindex,htransport,hgen,hfixed,hindividual,
    hquadA,hquadC,hcube,hbranch,hn,hback⟩ :=
      h.replacement_unequal_individual_fixed_root_at_neighbor d path hb hat hfirst hct
        hnormal hsmall hne
  refine ⟨g,hg,haw,hvw,hindex,htransport,hgen,hfixed,hindividual,
    hquadA,hquadC,hcube,?_,hn,hback⟩
  rcases hbranch with hlarge | ⟨hQ,hJ,hE,hcap⟩
  · exact Or.inl hlarge
  · refine Or.inr ⟨hQ,hJ,hE,hcap,?_⟩
    let w := act d.radical g⁻¹ t
    let v := act d.radical g⁻¹ c
    have hgS := Ltilde_le_stabilizer a hg
    have hUa : (U d.radical a).map (MulAut.conj g).toMonoidHom = U d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized a hgS)
    have hQa : (Q d.radical a).map (MulAut.conj g).toMonoidHom = Q d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hgS)
    have hJa : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom =
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical w) (Nat.card F^2) := by
      rw [Subgroup.SmallMover.join_map _ (MulAut.conj g).injective,hUa,hQa]
      simp only [w,Q_act,inv_inv]
    have hEc : (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom =
        Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical w) (Nat.card F^2) := by
      rw [Subgroup.SmallMover.join_map _ (MulAut.conj g).injective]
      simp only [v,w,U_act,Q_act,inv_inv]
    apply h.replacement_unequal_kernel_nonsplitting d geometry hb path.start_color haw hvw
      (fun he => hne (map_injective (MulAut.conj g).injective
        (hEc.trans (he.trans hJa.symm))))
    exact hQ.trans inf_le_right

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
