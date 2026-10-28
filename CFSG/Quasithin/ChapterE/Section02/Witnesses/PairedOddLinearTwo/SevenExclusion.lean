module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.LocalLift
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.Automizer
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.SubgroupSmallExclusion
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import GorensteinWalter.LinearRingEquiv

/-!
# Excluding the original paired PSL₂(7) small automizer

The paired core theorem identifies the original J with O₂(H). Elementary
Sylow-normal placement puts V in the normalizer of the chosen component.
The full preimage of the component-local subgroup is then a nonsolvable
minimal parabolic with a normal component, whose actual star image is the
original PSL₂(7). Its maximal subgroup lies in the original M and V remains
outside its core. All small-action and residual hypotheses restrict to this
subgroup. The proved PSL₂(7) ≃ PSL₃(2) identification now invokes the binary
linear-three source exclusion, without an extra local or marking premise.

Source: Aschbacher–Smith E.2.17, printed p.230, paired PSL₂(7) branch;
the local reduction uses the component geometry of E.2.2, pp.215–216.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
universe u
variable {H : Type u} [Group H] [Finite H] {D : Type*} [Group D] [Finite D]

theorem source_seven_small_automizer_false
    {κ : GroupClass.{u}}
    (hA : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremA κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬K.Normal)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 7)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) : False := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let TX := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let C := K.map q
  let W := V.map q
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hJ : J = pCore 2 H := Structure.PairedCore.source hA hH T hP hs hK hqK hgen hnot
  have hHX := (Structure.source_star_sqtk (hA H) hH T hP hs).stronglyQuasithin
  have hi := Structure.source_component_simple_image T hP hs K hK hgen
  let : IsSimpleGroup C := hi.1
  obtain ⟨hPX,hJX⟩ := Structure.source_star_minimal_core_free T hP
  have hsX : ¬ Group.IsSolvable (H ⧸ J) := fun hh =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hh⟩)
  have hrad : solvableRadical (H ⧸ J) = ⊥ := by
    rw [← ChapterB.minimalParabolic_nonsolvable_core_eq_radical TX hPX hsX]
    exact hJX
  have hTW : (TX : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
    (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hvn)).trans (le_normalizer_map q)
  obtain ⟨F,hF,hfin,hsize,⟨e⟩⟩ := hm
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hplace := source_component_placement (p := 7) (by decide) hsize (Or.inl rfl)
    hHX TX hPX hi.2.1 (hK.map_quotient J) hrad hi.2.2.2 e W (map_mono hVT) hTW
  have hVK : V ≤ normalizer (K : Set H) := by
    rw [←normalizer_cComponent_quotient hK J]
    exact map_le_iff_le_comap.mp hplace.1
  obtain ⟨L,hVL,hQL,S,hS,hPS,hsL,K0,hK0,hKn,hgen0,⟨eK⟩,hML,houtL⟩ :=
    source_component_local_geometry T hP hs K hK hgen hJ hHX V hVT hvn hout hVK
  let : K0.Normal := hKn
  let := Fintype.ofFinite F
  let eF : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hsize)
  let e' := ((eK.trans e).trans (GorensteinWalter.psl2RingEquiv eF).symm).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
  have hbinary : ClassicalGroup.IsPSL
      (K0.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore S hPS))) 3 2 :=
    ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨e'⟩⟩
  exact LinearThree.source_subgroup_binary_small_automizer_false T hP V hVT hvn hcore hfit hV
    U hTU hU f hf hk hD hratio hres L hVL hQL S hS hPS hsL K0 hK0 hgen0 hbinary hML houtL
end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
