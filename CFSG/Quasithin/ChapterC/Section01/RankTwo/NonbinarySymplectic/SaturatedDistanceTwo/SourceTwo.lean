module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceOne
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.FullCoreLayers
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.MaximizingPlane
public import Theory.Representation.SymplecticFourOrthogonalCover.QuadraticLifting

/-!
# The small-movement branch of MS93 (3.7)(2)

A two-subgroup of Sp₄(F) with natural fixed index at most q squared acts
quadratically. In Sylow coordinates it lies either in the plane radical
or in one of the quadratic planes of the point radical. Fixed-vector
lifting transfers this through the complete symplectic central cover.

Apply this to the entire opposite two-core. The full-layer decomposition
Z = U Z_t retains the common edge center, which centralizes that core.
Thus its action on Z is quadratic as well. Source (3.7)(1) makes the same
displacement centralize T₀; since T = T₀ Q, it lies in the actual midpoint
omega-center. Both complete fixed attachments remain in the argument.

This proves the first subcase of (3.7)(2), printed p.873, with its movement
bound on the actual natural cover. The large-movement subcase, subsequent
paired fixed-kernel comparisons and critical-pair selection remain before
the field restriction. Source: Meierfrankenfeld--Stellmacher (1993).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
open Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
open Representation.SymplecticFourOrthogonalCover

private theorem quadratic_of_small_natural_index
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (A : Subgroup (Sp F)) (hA : IsPGroup 2 A)
    (hsmall : 2 ^ fixedCodim (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := F) 2)) A ≤ Nat.card F^2) :
    ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v := by
  obtain ⟨S,hS⟩ := hA.exists_le_sylow
  let := Fintype.ofFinite F
  obtain ⟨n,hn,hFn⟩ := FiniteField.card F 2
  have hF : Nat.card F=2^(n:ℕ) := by simpa only [Nat.card_eq_fintype_card] using hFn
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) S (unipotentSylow hF n.pos)
  have hSm : (S : Subgroup (Sp F)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hg
  let B := A.map (MulAut.conj g).toMonoidHom
  have hBU : B ≤ unipotent := (map_mono hS).trans_eq hSm
  let E := B.subgroupOf unipotent
  have hEm : E.map unipotent.subtype=B := map_subgroupOf_eq_of_le hBU
  let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have hm : movingIndex E ≤ Nat.card F^2 := by
    rw [←binary_movingIndex]
    change 2^fixedCodim (τ.comp unipotent.subtype) E ≤ _
    rw [fixedCodim,fixedSpace_comp_map,hEm]
    change 2^fixedCodim τ (A.map (MulAut.conj g).toMonoidHom) ≤ _
    rw [fixedCodim_map_conj]
    exact hsmall
  have hq : ∀ x ∈ B, ∀ y ∈ B, ∀ v : Vector F, x • (y • v-v)=y • v-v := by
    rw [←hEm]
    by_cases hw : E ≤ wing true
    · exact fun x hx y hy v => Degree.plane_radical_quadratic x (map_mono hw hx)
        y (map_mono hw hy) v
    · obtain ⟨l,hl⟩ := Degree.exists_plane_coordinates_of_not_le_wing E hm hw
      have hEP : E ≤ finitePlane l := by
        intro x hx
        obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
        exact (element_mem_finitePlane l b u w v).mpr (hl b u w v hx)
      exact fun x hx y hy v => Degree.small_quadratic _ (Degree.small_finitePlane l)
        x (map_mono hEP hx) y (map_mono hEP hy) v
  have hh := Degree.quadratic_conjugate B g⁻¹ hq
  have hback : B.map (MulAut.conj g⁻¹).toMonoidHom=A := by
    dsimp only [B]
    rw [Subgroup.map_map]
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id (Sp F) := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]
  rwa [hback] at hh

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A two-subgroup moving at most q squared cosets of U acts quadratically
on its complete symplectic cover, including the full fixed kernel. -/
theorem moving_quadratic_of_small_index
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    {z : Vertex d.radical} (hz : color d.radical z = false)
    (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ stabilizer d.radical z)
    (hA : IsPGroup 2 A)
    (hsmall : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ (2^n)^2) :
    ⁅⁅U d.radical z,A⁆,A⁆ = ⊥ := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d hz
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g hb)
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let β := e.groupEquiv.toMonoidHom.comp (κC.comp (inclusion hAS))
  have hβ (x : A) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hAS x)))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hAS x) w
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hαr : α.range=β.range.map (commutator (Sp E.Carrier)).subtype :=
    MonoidHom.range_comp _ _
  have hαP : IsPGroup 2 α.range := hA.of_surjective α.rangeRestrict α.rangeRestrict_surjective
  have hi := embedded_centralizer_index (MovedSection.coverAction s e)
    (U d.radical z) A j hj hjr β hβ
  rw [hi,fixedCodim_of_binaryCover (MovedSection.coverProjection s e) he] at hsmall
  let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
  have hm := fixedCodim_map_equivariant (binaryNatural (K := E.Carrier)) τ
    (commutator (Sp E.Carrier)).subtype (LinearEquiv.refl _ _) (fun _ _ => rfl) β.range
  rw [←hαr] at hm
  rw [hm] at hsmall
  have hquad := quadratic_of_small_natural_index α.range hαP
    (by simpa only [E.card_eq,hE] using hsmall)
  apply embedded_quadratic_of_natural_quadratic (U d.radical z) A j hjr β
    (MovedSection.coverAction s e) hβ (MovedSection.coverProjection s e) he
  exact fun a b v => hquad (α a) ⟨a,rfl⟩ (α b) ⟨b,rfl⟩ v

/-- The small-movement subcase of MS93 (3.7)(2). Its index is measured
on the original opposite natural cover; the entire Q acts and the common
edge center and both complete fixed attachments are retained. -/
theorem source_two_of_small_core_movement
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hsmall : (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ (2^n)^2) :
    ⁅Z d.radical z,Q d.radical a⁆ ≤ Z d.radical t := by
  have hZzT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b d.radical
    omega
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hZt : Z d.radical t = omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hcentral : Z d.radical t ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [hZt]
    exact fun x hx y hy => (mem_omegaCenter_iff.mp hx).2.2 y (c.core_le_edge hy)
  have hUQ : U d.radical z ≤ normalizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    ((U_le_Z z).trans hZzT).trans (c.edge_le.trans (Q_normalized d.radical a))
  have heq : ⁅Z d.radical z,Q d.radical a⁆ = ⁅U d.radical z,Q d.radical a⁆ := by
    apply le_antisymm ?_ (commutator_mono (U_le_Z z) le_rfl)
    rw [commutator_comm (Z d.radical z),commutator_comm (U d.radical z)]
    apply commutator_le_moving_of_inner_mod_centralizer (Q d.radical a) (U d.radical z)
      (Z d.radical z) hUQ
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.end_color hzt]
    exact sup_le_sup_left hcentral _
  have hquad := moving_quadratic_of_small_index h d g (by omega) path.end_color
    (Q d.radical a) (c.core_le_edge.trans c'.edge_le)
    (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color) hsmall
  have hfull := (paired_source_triples h d g hb hsat path hat hzt c c').2.1
  have hcentralT : ⁅Z d.radical z,Q d.radical a⁆ ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←c.componentRadical_sup_core g (by omega)]
    apply sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hfull))
    apply le_centralizer_iff.mp
    rw [heq]
    exact commutator_eq_bot_iff_le_centralizer.mp hquad
  have hWZ : ⁅Z d.radical z,Q d.radical a⁆ ≤ Z d.radical z := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((c.core_le_edge.trans c'.edge_le).trans (Z_normalized d.radical z))
  have hZX := g.omega_bound z path.end_color (by
    rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)
  rw [hZt]
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hZzT (hWZ hx),
    (mem_omegaCenter_iff.mp (hZX (hWZ hx))).2.1,hcentralT hx⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
