module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootTrappedKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootFixedPaths

/-!
# Backward paths in the unequal-mover critical-root branch

The whole-X decomposition and the common Sylow fixed point bound the full
neighboring-seed index over the edge seed by q cubed. The trapped root's
fixed kernel is normalized by the same individual mover and endpoint;
individual residual generation and the small-section theorem place it in B.
Its index on U is at most q, contradicting the original moving index above q.

The actual selector therefore yields a backward critical path, retaining its
conjugator, both whole-Z fixed equalities, residual generation, quotient-image
growth and every overlap. Source: the unequal-mover case of MS93 (5.7),
printed p.919. The equal-mover case, remaining large-image selections and
terminal distance exclusions are separate; no distance-two conclusion is
asserted here.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.TwoLocalCover
open scoped commutatorElement IsMulCommutative
open Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four


namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open CentralRootGeometry.SmallMovers
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

/-- The full edge seed has index at most q cubed in each neighboring
seed in the critical-root branch, including all central attachments. -/
theorem Input.replacement_root_neighbor_seed_index_le_cube
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
    (Z d.radical t).relIndex (Z d.radical v) ≤ Nat.card F^3 := by
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [path.start_color] at hh
    cases ht : color d.radical t <;> simp_all
  have hZX := geometry.omega_bound a path.start_color (by
    rw [geometry.distance_constant a path.start_color]
    exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  have hZQ : Z d.radical a ≤ Q d.radical t :=
    (hZX.trans (omegaCenter_le _)).trans (Q_le_adjacent_h d.radical ht hat)
  have hTS : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 a (adjacent_symm _ hat)
  have hfix : Z d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ Z d.radical t := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      rw [Z,if_neg (by rw [ht]; decide)]
      exact mem_omegaCenter_iff.mpr ⟨hZQ hx,(mem_omegaCenter_iff.mp (hZX hx)).2.1,hc⟩
    · rintro ⟨hx,hz⟩
      rw [Z,if_neg (by rw [ht]; decide)] at hz
      exact ⟨hx,(mem_omegaCenter_iff.mp hz).2.2⟩
  have heidx : (Z d.radical t).relIndex (Z d.radical a) =
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) := by
    rw [←inf_relIndex_left,←hfix,inf_relIndex_left]
  let := X_elementary d.radical a
  let := finite_X d.radical a
  have hsplit := h.replacement_root_X_decomposition_center d path hb hsmall
  have hXidx := fixed_index_of_split (X d.radical a) (U d.radical a)
    (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (Q d.radical t) ((U_le_Z a).trans hZX) hsplit
    (inf_le_right.trans (centralizer_le hTS))
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb path.start_color hat
  have hcard : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hUS : U d.radical a ≤ stabilizer d.radical a := (U_le_Z a).trans (Z_le_stabilizer _ a)
  have hi := hidx ((Q d.radical t).subgroupOf (stabilizer d.radical a)) le_rfl
  rw [←Subgroup.SmallMover.centralizer_index_map (stabilizer d.radical a).subtype
    (stabilizer d.radical a).subtype_injective,
    map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS] at hi
  have hbound : (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^3 := by
    rw [hi,←hcard]
    let T := (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f).subgroupOf unipotent
    have hd := (fixed T).finrank_quotient_add_finrank
    have hlo := Submodule.finrank_mono (standardPoint_le_fixed T)
    rw [finrank_point] at hlo
    have hv : Module.finrank E.Carrier (CentralRootGeometry.SmallMovers.Vector (F := E.Carrier))=4 := by
      simp [CentralRootGeometry.SmallMovers.Vector]
    rw [hv] at hd
    apply Nat.pow_le_pow_right Nat.card_pos
    change Module.finrank E.Carrier (CentralRootGeometry.SmallMovers.Vector (F := E.Carrier) ⧸ fixed T) ≤ 3
    change Module.finrank E.Carrier (CentralRootGeometry.SmallMovers.Vector (F := E.Carrier) ⧸ fixed T) +
      Module.finrank E.Carrier (fixed T) = 4 at hd
    have hle : Module.finrank E.Carrier (CentralRootGeometry.SmallMovers.Vector (F := E.Carrier) ⧸ fixed T) + 1 ≤ 3 + 1 :=
      (Nat.add_le_add_left hlo _).trans_eq hd
    exact Nat.le_of_add_le_add_right hle
  have hbase : (Z d.radical t).relIndex (Z d.radical a) ≤ Nat.card F^3 := by
    rw [heidx]
    exact (relIndex_le_of_le_right hZX index_ne_zero_of_finite).trans (hXidx ▸ hbound)
  obtain ⟨g,hg,hga⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm _ hat) (adjacent_symm _ hvt)
  have hgt : act d.radical g t=t := hg
  have htransport : (Z d.radical t).relIndex (Z d.radical v)=
      (Z d.radical t).relIndex (Z d.radical a) := by
    conv_lhs => rw [←hga,←hgt]
    rw [Z_act,Z_act]
    exact relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective
  rwa [htransport]

/-- The source individual-generation branch cannot remain trapped once
the original B-relative moving index is greater than q. -/
theorem Input.replacement_unequal_trapped_root_excluded
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hgen : Ltilde d.radical a ≤
      Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical t) (Nat.card F^2) ⊔ Z d.radical z)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v)) :
    ¬ Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
  intro htrap
  let A := X d.radical z ⊓ Q d.radical a
  let D := (Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ⊔ Z d.radical a
  obtain ⟨hi,hEn,hZn⟩ := h.replacement_trapped_root_kernel_index_and_normalized d path hb hat hvt hn htrap
  have hDn : Ltilde d.radical a ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    hgen.trans (sup_le hEn hZn)
  have hDV : D ≤ V d.radical a :=
    (sup_le_sup inf_le_left le_rfl).trans (neighbor_seed_join_le_radius hat hvt)
  have hYV := neighbor_seed_join_le_radius hat hvt
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have haQ : Z d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    apply Z_le_Q_of_dist_lt _ a (geometry.exists_critical a path.start_color)
    rw [path.dist_start (Nat.sub_le _ _),geometry.distance_constant a path.start_color]
    have hh := path.length_eq_b
    change path.walk.length-2 < geometry.b d.radical
    omega
  have hYS : Z d.radical v ⊔ Z d.radical a ≤ stabilizer d.radical z :=
    (le_inf hYV (sup_le htrap haQ)).trans
      (truncated_radius_le_endpoint_stabilizer path (by omega))
  obtain ⟨_,hroot⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
    (by omega) (Z d.radical v) (le_sup_left.trans hYS) (le_sup_left.trans hYQ) hn
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2 := by
    rw [hroot]; nlinarith
  have hidx := (neighbor_seed_join_index_le geometry (by omega) path.start_color hat hvt).trans
    (h.replacement_root_neighbor_seed_index_le_cube d path hb hat hvt hsmall)
  have hYfin : Z d.radical v ⊔ Z d.radical a ≤ stabilizer d.radical a :=
    hYQ.trans (fun _ hx => hx.1)
  let := finite_stabilizer d.radical a
  let : Finite (Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hYfin) (inclusion_injective _)
  have hDi : (Z d.radical a).relIndex D < Nat.card F^4 :=
    lt_of_le_of_lt ((relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl)
      index_ne_zero_of_finite).trans hidx) ((pow_lt_pow_iff_right₀ hq).mpr (by decide))
  have hDB : D ≤ B d.radical a (geometry.Z_normal a) :=
    h.replacement_small_radius_le_B d geometry (by omega) path.start_color D hDV hDn hDi
  have hfixed : (U d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ≤
      B d.radical a (geometry.Z_normal a) :=
    ((inf_le_inf_right _ (U_le_Z v)).trans le_sup_left).trans hDB
  let := finite_Z d.radical v
  let : Finite (U d.radical v) := Finite.of_injective (inclusion (U_le_Z v)) (inclusion_injective _)
  have hidxB : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) ≤
      (U d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical v) :=
    relIndex_le_of_le_left hfixed index_ne_zero_of_finite
  rw [inf_relIndex_left] at hidxB
  exact (not_lt_of_ge (hidxB.trans hi)) hmove
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- In the unequal critical-root branch of (5.7), the same source selector
gives an actual backward critical path, with every overlap retained. -/
theorem Input.replacement_unequal_root_backward_path
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
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
      Ltilde d.radical a ≤ Ec ⊔ Z d.radical z ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      Z d.radical t ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅U d.radical a,Ja⁆,Ja⁆ = ⊥ ∧ ⁅⁅U d.radical v,Ec⁆,Ec⁆ = ⊥ ∧
      (centralizer (Ec : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F^3 ∧
      ¬ Q d.radical a ≤ Ec ∧ Nat.card F^2 < (Q d.radical a).relIndex Ec ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      (∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) := by
  have hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hidx := (neighbor_seed_join_index_le geometry (by omega) path.start_color hat hct).trans
      (h.replacement_root_neighbor_seed_index_le_cube d path hb hat hct hsmall)
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hBY := h.replacement_small_radius_le_B d geometry (by omega) path.start_color
      (Z d.radical c ⊔ Z d.radical a) (neighbor_seed_join_le_radius hat hct)
      ((Ltilde_le_stabilizer a).trans hn)
      (lt_of_le_of_lt hidx ((pow_lt_pow_iff_right₀ hq).mpr (by decide)))
    have hone := relIndex_eq_one.mpr (((U_le_Z c).trans le_sup_left).trans hBY)
    rw [hone] at hmove
    exact (not_lt_of_ge hq.le) hmove
  obtain ⟨g,hg,haw,hvw,hindex,htransport,hgen,hres,hfixed,hindividual,
    hquadA,hquadC,hcube,hnot,hlarge,hn,hback⟩ :=
      h.replacement_unequal_root_fixed_kernel_at_neighbor d path hb hat hfirst hct
        hnormal hsmall hne
  refine ⟨g,hg,haw,hvw,hindex,htransport,hgen,hres,hfixed,hindividual,
    hquadA,hquadC,hcube,hnot,hlarge,hn,?_⟩
  rcases hback with hback | htrap
  · exact hback
  · exact False.elim ((h.replacement_unequal_trapped_root_excluded d path hb haw hvw hn hres
      (hindex ▸ hmove)) htrap.1)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
