module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.SmallProduct
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.SmallPrimePower
public import Theory.SpecificGroups.PSL2.LargeOddProductInverter
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedOddLinearTwo.SmallImage
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
-- Internal coordinate adapter for the original maximal core J.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The field-seven restriction in the original exchanged odd row

The actual image VJ/J has order two and lies in the product of the two
conjugate PSL₂ components. For p greater than seven, its nonidentity
involution inverts an element of odd prime-power order greater than three
inside that same product. The original small-pair theorem forces this
order to be three. Thus the marked exchanged odd row has parameter seven.

Both the order-two image and the product placement are derived from the
original source data; no quotient recognition or inverter premise remains.
The residual-centralization hypothesis is not needed for this reduction.
Source: Aschbacher–Smith E.2.17, printed p.230. The remaining paired PSL₂(7)
solvable-subgroup exclusion is a separate source branch.
-/
public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
universe u v
variable {H : Type u} [Group H] [Finite H] {D : Type v} [Group D] [Finite D]
variable {κ : GroupClass.{u}}
private theorem source_parameter_eq_seven_of_card
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬ K.Normal)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p%8=1 ∨ p%8=7)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 p)
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
    (hcard : Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2) :
    p=7 := by
  by_contra hp7
  have hp9 : p ≠ 9 := by intro hh; subst p; norm_num at hp
  have hlarge : 9 < p := by have := hp.two_le; omega
  let : Fact p.Prime := ⟨hp⟩
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  obtain ⟨F,hF,hfin,hsize,⟨e⟩⟩ := hm
  obtain ⟨j,hj,hVj⟩ := source_star_product_embedding hA hH T hP hs K hK hgen hnot
    ho hsize (Or.inr hlarge) e V hVT hvn
  obtain ⟨v,hv,hvJ⟩ := Set.not_subset.mp hout
  have hv1 : q v ≠ 1 := fun hh => hvJ ((QuotientGroup.eq_one_iff v).mp hh)
  have hv2 : orderOf (q v) = 2 := orderOf_eq_prime (by
    rw [← map_pow,elemPow_eq_one_of_isElementaryAbelian (p:=2) v hv,map_one]) hv1
  obtain ⟨r,a,hr,hr2,ha,hbig,x,hx,hi⟩ :=
    Theory.PSL2.exists_large_odd_prime_power_inverted_of_product_embedding
      ho (n:=1) (by simpa using hsize) (by omega) (by simpa only [hsize] using hmod)
      j hj (q v) hv2 (hVj (mem_map_of_mem q hv))
  have hh := Involution.source_prime_power_inverter_eq_three T hP V hVT hvn hcore hout
    hfit hV U hTU hU f hf hk hD hratio hcard hr hr2 ha (q v) x
    (mem_map_of_mem q hv) hv1 hx hi
  omega
theorem source_small_parameter_eq_seven
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬ K.Normal)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p%8=1 ∨ p%8=7)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 p)
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
    : p=7 := by
  have hlarge : 7 ≤ p := by have := hp.two_le; omega
  have hc := source_image_card_two hA hH T hP hs K hK hgen hnot hp ho hlarge hm
    V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio
  exact source_parameter_eq_seven_of_card hA hH T hP hs K hK hgen hnot hp ho hmod hm
    V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio hc

theorem source_exchanged_odd_seven_model
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬ K.Normal)
    (hm : Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedOddModel
      (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H))
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
    : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 7 := by
  obtain ⟨p,hp,ho,hmod,hm,_,_⟩ := hm
  have he := source_small_parameter_eq_seven hA hH T hP hs K hK hgen hnot hp ho hmod hm
    V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio
  exact he ▸ hm
/-- The raw exchanged odd row forces parameter seven from the literal
prime lower bound; no residue-class assumption is required. -/
theorem source_small_parameter_eq_seven_of_seven_le
    (hA : ChapterA.Section02.TheoremA κ H) (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hnot : ¬ K.Normal)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hseven : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 2 p)
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
    : p=7 := by
  have hcard := source_image_card_two hA hH T hP hs K hK hgen hnot hp ho hseven hm
    V hVT hvn hcore hout hfit hV U hTU hU f hf hk hD hratio
  by_contra hp7
  have hp9 : p ≠ 9 := by intro hh; subst p; norm_num at hp
  have hlarge : 9 < p := by have := Nat.odd_iff.mp ho; omega
  let : Fact p.Prime := ⟨hp⟩
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  obtain ⟨F,hF,hfin,hsize,⟨e⟩⟩ := hm
  obtain ⟨j,hj,hVj⟩ := source_star_product_embedding hA hH T hP hs K hK hgen hnot
    ho hsize (Or.inr hlarge) e V hVT hvn
  obtain ⟨v,hv,hvJ⟩ := Set.not_subset.mp hout
  have hv1 : q v ≠ 1 := fun hh => hvJ ((QuotientGroup.eq_one_iff v).mp hh)
  have hv2 : orderOf (q v) = 2 := orderOf_eq_prime (by
    rw [← map_pow,elemPow_eq_one_of_isElementaryAbelian (p:=2) v hv,map_one]) hv1
  obtain ⟨r,a,hr,hr2,ha,hbig,x,hx,hi⟩ :=
    Theory.PSL2.exists_large_odd_prime_power_inverted_of_product_embedding_of_odd
      ho (n:=1) (by simpa using hsize) (by omega)
      j hj (q v) hv2 (hVj (mem_map_of_mem q hv))
  have hh := Involution.source_prime_power_inverter_eq_three T hP V hVT hvn hcore hout
    hfit hV U hTU hU f hf hk hD hratio hcard hr hr2 ha (q v) x
    (mem_map_of_mem q hv) hv1 hx hi
  omega

end CFSG.Quasithin.ChapterE.Witnesses.PairedOddLinearTwo
