module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRetainedN1Intersection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootLayers
public import Theory.SpecificGroups.SymplecticFour.RetainedPointRootPair
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualSelection

/-!
# Actual N1 generation in the retained marked unequal branch

Use the original quotient and its aligned point marking on the same residual
selector. A failed join produces the marked index-two root pair, so the full
original Q lies in the original unequal mover. That forces whole-X nonsplitting,
contradicting the internally established b=4 root decomposition. Thus the same
individual far mover and the same full endpoint contain the residual.

The point projection, incident plane marking and endpoint position are explicit
source certificates. They are not inferred from a three-generator equality.
No endpoint or selector is changed, and no radius-fixed premise is used.
Source: MS93 (5.5)(c), printed pp.915--917, and the N1 step on p.925.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The original N1 join contains the residual when its actual marked
point projection and incident plane placement are retained. -/
theorem Input.replacement_distance_four_retained_N1_generation
    {geometry : Geometry d.radical} {u e a t : Vertex d.radical}
    (back : CriticalPath d.radical geometry u e) (hb : geometry.b d.radical=4)
    (hut : Adjacent d.radical u t) (hat : Adjacent d.radical a t)
    (hne : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical t) (Nat.card F^2))
    (r : FreeAmalgam d.radical) (hr : r ∈ Ltilde d.radical u)
    (B : BinaryField) (hB : B.degree=n)
    (f₀ f : stabilizer d.radical u →* Sp B.Carrier)
    (hf₀ : Function.Surjective f₀)
    (hf₀Q : f₀.ker.map (stabilizer d.radical u).subtype=Q d.radical u)
    (hfQ : f.ker.map (stabilizer d.radical u).subtype=Q d.radical u)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical u)).map f₀ ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical u),
      (centralizer (A : Set (stabilizer d.radical u))).relIndex
        ((U d.radical u).subgroupOf (stabilizer d.radical u)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f₀))
    (w : Sp B.Carrier)
    (htransport : ((Subgroup.SmallMover.join (U d.radical (act d.radical r a))
        (Q d.radical (act d.radical r a)) (Q d.radical (act d.radical r t))
        (Nat.card F^2)).subgroupOf (stabilizer d.radical u)).map f =
      (((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical u)).map f₀).map
          (MulAut.conj w).toMonoidHom)
    (hproj : ((((Z d.radical e).subgroupOf (stabilizer d.radical u)).map f ⊔
      ((Subgroup.SmallMover.join (U d.radical (act d.radical r a))
        (Q d.radical (act d.radical r a)) (Q d.radical (act d.radical r t))
        (Nat.card F^2)).subgroupOf (stabilizer d.radical u)).map f).subgroupOf
          pointLocal).map pointQuotient=⊤)
    (hcore : (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤ pointLocal)
    (k : Sp B.Carrier) (hk : k∈planeLocal) (hkp : k∉pointParabolic)
    (hwk : w*k∈pointLocal)
    (hAL : ((Z d.radical e).subgroupOf (stabilizer d.radical u)).map f ≤ pointLocal)
    (hAproj : ((((Z d.radical e).subgroupOf (stabilizer d.radical u)).map f).subgroupOf
      pointLocal).map pointQuotient=Matrix.SpecialLinearGroup.upperUnipotent B.Carrier)
    (hlarge : Nat.card F^2 ≤ (Q d.radical u).relIndex (Z d.radical e)) :
    Ltilde d.radical u ≤
      Subgroup.SmallMover.join (U d.radical (act d.radical r a))
        (Q d.radical (act d.radical r a)) (Q d.radical (act d.radical r t))
        (Nat.card F^2) ⊔ Z d.radical e := by
  by_contra hfail
  let S := stabilizer d.radical u
  let E₀ := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E := (E₀.subgroupOf S).map f₀
  let E₁ := E.subgroupOf unipotent
  let v := act d.radical r a
  let s := act d.radical r t
  let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
    (Q d.radical s) (Nat.card F^2)
  let A := (Z d.radical e).subgroupOf S
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hru : act d.radical r u=u := Ltilde_le_stabilizer u hr
  have hus : Adjacent d.radical u s := by
    rw [←hru]
    exact (adjacent_act_iff d.radical r _ _).mpr hut
  have hvs : Adjacent d.radical v s := (adjacent_act_iff d.radical r _ _).mpr hat
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 u (adjacent_symm _ hut)
  have hE₀S : E₀ ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 u (adjacent_symm _ hus))
  have hAS : Z d.radical e ≤ S := back.endpoint_Z_le_start_stabilizer (by omega)
  have hEU : E ≤ unipotent :=
    (map_mono (comap_mono (Subgroup.SmallMover.join_le _ _ _ _))).trans hTf
  have hE₁ : E₁.map unipotent.subtype=E := map_subgroupOf_eq_of_le hEU
  have hBF : Nat.card B.Carrier=Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hUS : U d.radical u ≤ S := (U_le_Z u).trans (Z_le_stabilizer d.radical u)
  have hmove : movingIndex E₁ =
      (centralizer (E₀ : Set (FreeAmalgam d.radical))).relIndex (U d.radical u) := by
    rw [←binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) E₁ = _
    rw [fixedCodim,fixedSpace_comp_map,hE₁]
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical u).subgroupOf S) (E₀.subgroupOf S)
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hE₀S,hindex] at hh
    exact hh.symm
  have hbig : Nat.card B.Carrier^2 < movingIndex E₁ := by
    rw [hmove,hBF]
    exact (h.replacement_unequal_individual_indices d geometry hb4 back.start_color hut hat hne).2
  have hEfixed : fixed E₁=point B.Carrier :=
    (fixed_eq_point_and_movingIndex_of_square_lt E₁ hbig).1
  have hker : f.ker=(Q d.radical u).subgroupOf S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical u ≤ S from fun _ hx => hx.1)]
  have hQp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (Q_isPGroup d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) u back.start_color).comap_subtype
  let : IsElementaryAbelian 2 (Z d.radical e) := geometry.Z_elementary (by omega) e back.end_color
  have hAp : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z d.radical e)).comap_subtype
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) back.start_color hus
  have hQs : Q d.radical u ≤ Q d.radical s := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hTv : Q d.radical s ≤ stabilizer d.radical v :=
    fun _ hx => hx.2 v (adjacent_symm _ hvs)
  have hTJ : Q d.radical s ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    (le_inf (le_inf (hTv.trans (U_normalized v)) (hTv.trans (Q_normalized d.radical v)))
      (Q d.radical s).le_normalizer).trans (Subgroup.SmallMover.normalizer_join _ _ _ _)
  have hQn : f.ker ≤ normalizer (J.subgroupOf S : Set S) := by
    rw [hker]
    exact (comap_mono (hQs.trans hTJ)).trans (J.le_normalizer_comap S.subtype)
  have hproper : A.map f ⊔ (E₁.map unipotent.subtype).map (MulAut.conj w).toMonoidHom ≠ ⊤ := by
    intro htop
    have hfull : (J.subgroupOf S ⊔ A).map f=⊤ := by
      rw [Subgroup.map_sup,htransport,sup_comm]
      simpa only [hE₁] using htop
    have hres := map_mono (f := S.subtype)
      (residual_le_individual_join f (J.subgroupOf S) A hQp hAp hQn hfull)
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hAS] at hres
    exact hfail hres
  have hprojection : ((A.map f ⊔ (E₁.map unipotent.subtype).map
      (MulAut.conj w).toMonoidHom).subgroupOf pointLocal).map pointQuotient=⊤ := by
    rw [hE₁]
    exact htransport ▸ hproj
  have hout : ¬ E₁.map unipotent.subtype ≤
      (CentralRootGeometry.wing true).map unipotent.subtype := by
    intro hle
    have hwingle : E₁ ≤ CentralRootGeometry.wing true :=
      (map_le_map_iff_of_injective unipotent.subtype_injective).mp hle
    exact hbig.not_ge (movingIndex_le_field_sq_of_le_wing E₁ hwingle)
  have hAlarge : Nat.card B.Carrier^2 ≤ Nat.card (A.map f) := by
    have hh := relIndex_map_map_of_injective f.ker A S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hAS,relIndex_ker] at hh
    rw [hBF,←hh]
    exact hlarge
  obtain ⟨b,c,hc,hpair⟩ := RetainedPointRootPair.original_mover_root_pair B.card_eq
    (by rw [hB]; exact h.nonbinary) (A.map f) E₁ hEfixed hout k w hk hkp hwk
    hproper hprojection hcore hAL hAproj hAlarge
  rw [hE₁] at hpair
  have hQa := h.replacement_root_pair_index_two_kernel d geometry hb4 back.start_color
    hut hat B hB f₀ hf₀ hf₀Q hindex (some b) (some (b+c)) (by simpa using hc) hpair
  exact h.replacement_unequal_kernel_nonsplitting d geometry hb4 back.start_color
    hut hat hne hQa (h.replacement_distance_four_X_split d geometry hb back.start_color)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
