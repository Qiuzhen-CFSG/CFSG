module
public import Stellmacher.SectionNine.NineFourAuxiliaryActivation
public import Theory.GroupTheory.CommutatorPreimage
public import Mathlib.Tactic.Group

/-!
# The invariant residual support of the auxiliary module in (9.4)

For the source group F and each selected y in A, the literal auxiliary
subgroup V_y is normalized by F and lies in [V_next,O²(F)] Z_next. Only
the actual normalized remote adjacency and original commutator bound
are used, so this applies before the central/noncentral case split.

F normalizes both <y>V_next and its own residual two-core Q; consequently
it normalizes their commutator and its join with Z_next. The local odd
quotient and residual perfection give Q=[Q,O²(F)]. To apply the relative
three-subgroups lemma, we show that <y>V_next normalizes
[V_next,O²(F)]: conjugation moves a residual actor only by an element of
the abelian V_next, which leaves its commutator module unchanged. Both
rotated commutators then lie in [V_next,O²(F)] Z_next.

These are the two auxiliary-module facts just before source (9.4)(3),
printed p.51/PDF p.41 of `refs/files/stellmacher-n-group.pdf`.
-/

open scoped commutatorElement IsMulCommutative
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem commutator_sup_right_le
    {G : Type*} [Group G] (P X Y V K : Subgroup G)
    (hPK : P ≤ Subgroup.normalizer K) (hXP : X ≤ P) (hYP : Y ≤ P)
    (hVX : ⁅V,X⁆ ≤ K) (hVY : ⁅V,Y⁆ ≤ K) : ⁅V,X⊔Y⁆ ≤ K := by
  rw [Subgroup.commutator_comm]
  have hx : X ≤ Subgroup.commutatorPreimage P V K :=
    Subgroup.le_commutatorPreimage hXP (by simpa only [Subgroup.commutator_comm] using hVX)
  have hy : Y ≤ Subgroup.commutatorPreimage P V K :=
    Subgroup.le_commutatorPreimage hYP (by simpa only [Subgroup.commutator_comm] using hVY)
  exact (Subgroup.commutator_mono (sup_le hx hy) le_rfl).trans
    (Subgroup.commutator_commutatorPreimage_le P V K hPK)

private theorem normalizes_commutator_of_abelian_layer
    {G : Type*} [Group G] (U V R : Subgroup G) [IsMulCommutative V]
    (hUV : U ≤ Subgroup.normalizer V) (hUR : ⁅U,R⁆ ≤ V) :
    U ≤ Subgroup.normalizer (⁅V,R⁆ : Subgroup G) := by
  let K := ⁅V,R⁆
  have hVVR : ⁅V,V⊔R⁆ ≤ K := by
    apply commutator_sup_right_le (V⊔R) V R V K
      (sup_le (Subgroup.normalizer_commutator_ge_left V R)
        (Subgroup.normalizer_commutator_ge_right V R)) le_sup_left le_sup_right ?_ le_rfl
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (show V ≤ Subgroup.centralizer (V : Set G) from fun x hx y hy =>
        setLike_mul_comm (s:=V) hy hx)).le.trans bot_le
  apply Subgroup.le_normalizer_iff.mpr
  intro u hu k hk
  have hVmap : V.map (MulAut.conj u).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUV hu)
  have hRmap : R.map (MulAut.conj u).toMonoidHom ≤ V⊔R := by
    rintro r ⟨r,hr,rfl⟩
    have hc : ⁅u,r⁆ ∈ V := hUR (Subgroup.commutator_mem_commutator hu hr)
    have heq : u*r*u⁻¹ = ⁅u,r⁆*r := by simp [commutatorElement_def]
    change u*r*u⁻¹ ∈ V⊔R
    rw [heq]
    exact (V⊔R).mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hr)
  have hmap : K.map (MulAut.conj u).toMonoidHom ≤ K := by
    rw [Subgroup.map_commutator,hVmap]
    exact (Subgroup.commutator_mono le_rfl hRmap).trans hVVR
  exact hmap (Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hk)

private theorem auxiliary_residual_support_algebra
    {G : Type*} [Group G] (U V R Q Z : Subgroup G) [IsMulCommutative V]
    (hUV : U ≤ Subgroup.normalizer V) (hUZ : U ≤ Subgroup.normalizer Z)
    (hRZ : R ≤ Subgroup.normalizer Z) (hQR : Q ≤ R)
    (hcore : Q = ⁅Q,R⁆) (hUQ : ⁅U,Q⁆ ≤ V)
    (hUR : ⁅U,R⁆ ≤ V) (hVQ : ⁅V,Q⁆ ≤ Z) :
    ⁅U,Q⁆ ⊔ Z ≤ ⁅V,R⁆ ⊔ Z := by
  let K := ⁅V,R⁆ ⊔ Z
  have hUK : U ≤ Subgroup.normalizer K :=
    (le_inf (normalizes_commutator_of_abelian_layer U V R hUV hUR) hUZ).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hRK : R ≤ Subgroup.normalizer K :=
    (le_inf (Subgroup.normalizer_commutator_ge_right V R) hRZ).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hUQK : ⁅U,Q⁆ ≤ K := by
    have hh : ⁅⁅Q,R⁆,U⁆ ≤ K := by
      apply Subgroup.commutator_commutator_le_of_rotate_of_le_normalizer
        (hQR.trans hRK) hRK hUK
      · have hRU : ⁅R,U⁆ ≤ V := by simpa only [Subgroup.commutator_comm] using hUR
        exact (Subgroup.commutator_mono hRU le_rfl).trans (hVQ.trans le_sup_right)
      · exact (Subgroup.commutator_mono hUQ le_rfl).trans le_sup_left
    rwa [← hcore,Subgroup.commutator_comm] at hh
  exact sup_le hUQK le_sup_right


public theorem nine_four_auxiliary_residual_support
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (A : Subgroup G) (hA : A ≤ VAt ctx.Γ remote)
    (hcomm : ⁅A, Subgroup.zpowers actor⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (y : G) (hy : y ∈ A)
 :
    let F := (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote) ⊔
      Subgroup.zpowers actor
    let Q := twoCoreIn (twoResidualIn F)
    let V_y := ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep, Q⁆ ⊔
      ZAt ctx.Γ ctx.criticalPath.firstStep
    F ≤ Subgroup.normalizer (V_y : Set G) ∧
      V_y ≤ ⁅VAt ctx.Γ ctx.criticalPath.firstStep, twoResidualIn F⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let F := (QAt Γ cp.a ⊓ QAt Γ remote) ⊔ Subgroup.zpowers actor
  let R := twoResidualIn F
  let Q := twoCoreIn R
  let U := Subgroup.zpowers y ⊔ V
  let W := ⁅U,Q⁆ ⊔ Z
  have hgeom := nine_four_auxiliary_core_geometry ctx hb remote actor hactor
  have hFP : F ≤ P := hgeom.1
  have hRF : R ≤ F := twoResidualIn_le F
  have hQR : Q ≤ R := twoCoreIn_le R
  have hPQ : P ≤ Subgroup.normalizer Z := stabilizer_le_normalizer_z Γ cp.firstStep
  have hodd : Odd (Nat.card (R ⧸ pCore 2 R)) :=
    local_residual_core_quotient_odd ctx.sectionSeven Γ cp.firstStep cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)) F hFP
  have hcoreComm : Q = ⁅Q,R⁆ := by
    have hh := congrArg (Subgroup.map R.subtype)
      (twoCore_eq_commutator_of_residual_perfect
        (twoResidualAmbient_has_top_twoResidual F) hodd)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    exact hh
  have hyD : y ∈ VAt Γ remote := hA hy
  have hCy : Subgroup.zpowers y ≤ VAt Γ remote := Subgroup.zpowers_le.mpr hyD
  have hCyA : Subgroup.zpowers y ≤ A := Subgroup.zpowers_le.mpr hy
  have hCyComm : ⁅Subgroup.zpowers y, Subgroup.zpowers actor⁆ ≤ V :=
    (Subgroup.commutator_mono hCyA le_rfl).trans hcomm
  have hnorm := nine_four_auxiliary_normalization ctx hb remote hremote actor hactor
    (Subgroup.zpowers y) hCy hCyComm
  have hUR : ⁅U,R⁆ ≤ V := (Subgroup.commutator_mono le_rfl hRF).trans hnorm.2
  have hVQ : ⁅V,Q⁆ ≤ Z :=
    (Subgroup.commutator_mono le_rfl hgeom.2.1).trans_eq
      (nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1, Γ.act_one _⟩).2.1
  have hb2 : 2 < cp.length := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change Odd cp.length at hodd
    obtain ⟨k,hk⟩ := hodd
    change 1 < cp.length at hb
    omega
  have hDQa : VAt Γ remote ≤ QAt Γ cp.a :=
    (nine_seven_neighbor_module_le_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mp hremote)).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext hb2 cp.a)
  have hQaP : QAt Γ cp.a ≤ P :=
    ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans
      cp.S_le_edge_stabilizers).trans inf_le_right
  have hVP : V ≤ P := (nine_seven_module_le_own_core ctx.toLocalContext hb cp.firstStep).trans
    (by change q Γ cp.firstStep ≤ stabilizer Γ cp.firstStep
        rw [q, Γ.twoCoreAt_def]
        exact twoCoreIn_le _)
  have hUP : U ≤ P := sup_le (hCy.trans (hDQa.trans hQaP)) hVP
  let _ : IsElementaryAbelian 2 V :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have hFComm : F ≤ Subgroup.normalizer (⁅U,Q⁆ : Subgroup G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro f hf c hc
    have hUm : U.map (MulAut.conj f).toMonoidHom = U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnorm.1 hf)
    have hQm : Q.map (MulAut.conj f).toMonoidHom = Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hgeom.2.2.2 hf)
    have hmap : (⁅U,Q⁆).map (MulAut.conj f).toMonoidHom = ⁅U,Q⁆ := by
      rw [Subgroup.map_commutator, hUm, hQm]
    have hm := Subgroup.mem_map_of_mem (MulAut.conj f).toMonoidHom hc
    rw [hmap] at hm
    exact hm
  have hFW : F ≤ Subgroup.normalizer W :=
    (le_inf hFComm (hFP.trans hPQ)).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hUQ : ⁅U,Q⁆ ≤ V :=
    (Subgroup.commutator_mono le_rfl (hQR.trans hRF)).trans hnorm.2
  exact ⟨hFW, auxiliary_residual_support_algebra U V R Q Z
    (hUP.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
    (hUP.trans hPQ) (hRF.trans (hFP.trans hPQ)) hQR hcoreComm hUQ hUR hVQ⟩

end Stellmacher.SectionNine
