module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearThree.BinarySectionSource
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.OddResidual
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.OriginalImage

/-!
# The original paired odd-linear image has order two

The paired component construction supplies a dihedral witness whose two-residual
has odd order in the actual quotient H/J. Lifting this witness places its
quaternion core in J. The image of V therefore factors through the pair's
order-six quotient, forcing its nontrivial two-group image to have order two.
No coordinate projection or image-cardinality condition is assumed.

Source: Aschbacher–Smith E.2.17, printed p.230, exchanged PSL₂(p) branch.
The only earlier-source input retained is the genuine Theorem A used to
transfer strong quasithinness through the actual maximal core.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

theorem OriginalWitness.small_image_card_two_of_odd_star_residual
    {T : Sylow 2 H} (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {V U : Subgroup H} [IsElementaryAbelian 2 V] {n : ℕ}
    (w : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n)
    (hVT : V ≤ (T : Subgroup H))
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (hodd : Odd (Nat.card ((pResidual 2 w.pair.subgroup).map
      ((QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)).comp w.pair.subgroup.subtype)))) :
    Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2 := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let W := V.map q
  have hPJ := (w.small_core_placement_of_odd_star_residual hP hVT hTV hcore hout hfit hV
    hTU hU f hf hk hD hratio hodd).1.trans (ChapterB.minimalParabolicTwoCore_le_core T hP)
  have hker : pCore 2 w.pair.subgroup ≤ (q.comp w.pair.subgroup.subtype).ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff (x:H)).mpr (hPJ (mem_map_of_mem w.pair.subgroup.subtype hx))
  let q' := QuotientGroup.lift (pCore 2 w.pair.subgroup) (q.comp w.pair.subgroup.subtype) hker
  have hW : W ≤ q'.range := by
    rintro x ⟨v,hv,rfl⟩
    exact ⟨QuotientGroup.mk' (pCore 2 w.pair.subgroup) ⟨v,w.pair.le hv⟩,rfl⟩
  have hn := ChapterE.minimalParabolic_normalizer_le T hP V
    (IsElementaryAbelian.isPGroup 2 V) hTV hout
  obtain ⟨e⟩ := (w.small_quaternion_core hVT hTV hcore hn hfit hV hTU hU f hf hk hD hratio).2.2.2.1
  have hcard : Nat.card (w.pair.subgroup ⧸ pCore 2 w.pair.subgroup) = 6 := by
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
  have hd : Nat.card W ∣ 6 := by
    rw [←hcard]
    exact (card_dvd_of_le hW).trans (card_range_dvd q')
  obtain ⟨m,hm⟩ := ((IsElementaryAbelian.isPGroup 2 V).map q).exists_card_eq
  have hcop : Nat.Coprime (Nat.card W) 3 := by
    rw [hm]
    exact (by decide : Nat.Coprime 2 3).pow_left m
  have hd2 : Nat.card W ∣ 2 := hcop.dvd_of_dvd_mul_right hd
  have hne : W ≠ ⊥ := by
    intro hh
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff V).mp hh)
  exact ((Nat.dvd_prime Nat.prime_two).mp hd2).resolve_left (fun hc => hne (card_eq_one.mp hc))
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement

namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
open BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]

theorem source_image_card_two
    {κ : GroupClass} (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬K.Normal)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 p)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk)) :
    Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2 := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let C := K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let : Group.IsSolvable J := ChapterB.minimalParabolic_core_solvable T hP
  let : Fact p.Prime := ⟨hp⟩
  have hsX : ¬Group.IsSolvable (H ⧸ J) := fun hx =>
    hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hx⟩)
  have hi := Structure.source_component_simple_image T hP hs K hK hgen
  let : IsSimpleGroup C := hi.1
  have hnC : ¬C.Normal := fun hc => hnot (cComponent_normal_of_quotient_normal hK J hc)
  obtain ⟨hPs,hJs⟩ := Structure.source_star_minimal_core_free T hP
  have hmax : ChapterB.minimalParabolicMax S hPs = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hSW : (S : Subgroup (H ⧸ J)) ≤ normalizer (W : Set (H ⧸ J)) :=
    (map_mono hTV).trans (le_normalizer_map q)
  have hWcore : W ≤ (ChapterB.minimalParabolicMax S hPs).pCoreIn 2 := by
    rw [hmax]
    exact (map_mono hcore).trans
      (Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le q M)
  have hWne : W ≠ ⊥ := by
    intro he
    exact hout (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff V).mp he)
  have hplarge : p=7 ∨ 9<p := by
    by_contra! hh
    have hupper : p ≤ 9 := hh.2
    interval_cases p <;> norm_num at *
    exact (by decide : ¬Nat.Prime 9) hp
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hw := source_pair_odd_residual ho hF hplarge
    (Structure.source_star_sqtk hA hH T hP hs).stronglyQuasithin S hPs hsX hJs
    hi.2.1 (hK.map_quotient J) hi.2.2.2 hnC e W (map_mono hVT) hSW hWcore hWne
  rw [hmax] at hw
  obtain ⟨w,hodd⟩ := hw
  obtain ⟨w',r,hr,hrq,ξ,_⟩ := QuotientLift.lift_pair T hP V hVT hvn hcore w.toPair
  let b : OriginalWitness T M V 1 :=
    ⟨w',1,by decide,one_dvd _,.dihedral rfl w.prime w.degree w.prime_prime w.prime_odd
      w.degree_pos (ξ.trans w.model)⟩
  have heq : q.comp w'.subgroup.subtype = w.subgroup.subtype.comp r := by
    ext x
    exact (hrq x).symm
  have hodd' : Odd (Nat.card ((pResidual 2 b.pair.subgroup).map
      (q.comp b.pair.subgroup.subtype))) := by
    change Odd (Nat.card ((pResidual 2 w'.subgroup).map (q.comp w'.subgroup.subtype)))
    rw [heq,←map_map,map_pResidual_of_surjective 2 r hr,
      card_map_of_injective w.subgroup.subtype_injective]
    exact hodd
  exact b.small_image_card_two_of_odd_star_residual hP hVT hTV hcore hout hfit hV
    hTU hU f hf hk hD hratio hodd'
end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
