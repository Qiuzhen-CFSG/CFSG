module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.OppositeAction
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedNormalizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The original marked order-sixteen torus acts fully on the five-plane

The actual image I of the first endpoint's C₄×C₄ normalizes each fixed
five-subgroup and its canonical core. It therefore normalizes the edge
B₅ C_P(u) and the actual opposite SL₂(5). Restriction to the two order-five
factors is injective: the kernel centralizes the self-centralizing edge,
and a subgroup of order16 meets that order25 edge trivially. Both cyclic
automorphism groups have order4, so restriction is an equivalence onto
their full product. Its two evaluation equations retain ambient conjugation.

The endpoint, central involution and five-subgroup markings are the genuine
preceding F.1.12 data; ambient fusion of the same u is supplied by the
marked short-path transport in FiveHexagon.PathTransport. No model for the
generated completion is used.

Source: Aschbacher–Smith, discussion preceding J.4.8–9, printed pp.442–443.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

omit [Finite G] in
private theorem sourceI_commute {x y:G} (hx:x∈sourceI e) (hy:y∈sourceI e) : Commute x y := by
  obtain ⟨a⟩ := sourceI_equiv e
  have he : (⟨x,hx⟩:sourceI e)*⟨y,hy⟩=⟨y,hy⟩*(⟨x,hx⟩:sourceI e) := by
    apply a.injective
    rw [map_mul,map_mul,mul_comm]
  exact congrArg Subtype.val he

omit [Finite G] in
private theorem normalizes_fixed {I P:Subgroup G} {v:G}
    (hIP:I≤normalizer (P:Set G)) (hvc:I≤centralizer ({v}:Set G)) :
    I≤normalizer ((P⊓centralizer ({v}:Set G) : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro r hr x hx
  refine ⟨(mem_normalizer_iff.mp (hIP hr) x).mp hx.1,?_⟩
  have hv : MulAut.conj r v=v := by
    change r*v*r⁻¹=v
    rw [mem_centralizer_singleton_iff.mp (hvc hr),mul_inv_cancel_right]
  apply mem_centralizer_singleton_iff.mpr
  have he := congrArg (MulAut.conj r) (mem_centralizer_singleton_iff.mp hx.2)
  simpa only [map_mul,hv,MulAut.conj_apply] using he

omit [Finite G] in
private theorem normalizes_core {I A:Subgroup G} (hIA:I≤normalizer (A:Set G)) :
    I≤normalizer (coreAt A : Set G) := by
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (coreAt A).map (MulAut.conj r).toMonoidHom=coreAt A
  have he : A.map (MulAut.conj r).toMonoidHom=A :=
    mem_normalizer_iff_map_conj_eq.mp (hIA hr)
  rw [map_coreAt,he]

/-- The actual marked I preserves each of the original fixed five-subgroups. -/
theorem sourceI_normalizes_fixed
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (v:G) (hv:v∈sourceI e) :
    sourceI e≤normalizer (fixedFive B5 v : Set G) := by
  apply normalizes_fixed
  · exact (sourceI_le_normalizer B5 e hfive).trans
      (normalizer_B5Image_le_normalizer_fiveOddPart B5)
  · intro r hr
    exact mem_centralizer_singleton_iff.mpr (sourceI_commute e hr hv).eq

/-- The same I preserves the canonical opposite core and its selected fixed factor. -/
theorem sourceI_normalizes_next
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    sourceI e≤normalizer (nextFive c B5 (sourceU e) : Set G) := by
  have hmarks := source_marks_mem c e hz
  apply normalizes_fixed
  · exact normalizes_core (sourceI_normalizes_fixed B5 e hfive _ hmarks.2)
  · intro r hr
    exact mem_centralizer_singleton_iff.mpr
      (sourceI_commute e hr ((sourceI e).mul_mem hmarks.1 hmarks.2)).eq

omit [Finite G] in
private theorem normalizes_sup {I A B:Subgroup G}
    (hA:I≤normalizer (A:Set G)) (hB:I≤normalizer (B:Set G)) :
    I≤normalizer ((A⊔B : Subgroup G) : Set G) := by
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (hA hr),
    mem_normalizer_iff_map_conj_eq.mp (hB hr)]

/-- The transported I normalizes the actual five-plane and its opposite SL₂ pair. -/
theorem sourceI_normalizes_edge_and_opposite
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    sourceI e≤normalizer (edge B5 (sourceU e) : Set G) ∧
      sourceI e≤normalizer (oppositePair c B5 (sourceU e) : Set G) := by
  have hm := source_marks_mem c e hz
  refine ⟨normalizes_sup (sourceI_le_normalizer B5 e hfive)
    (sourceI_normalizes_fixed B5 e hfive _ hm.2),?_⟩
  exact normalizes_sup
    (sourceI_normalizes_fixed B5 e hfive _ ((sourceI e).mul_mem hm.1 hm.2))
    (sourceI_normalizes_next c B5 e hz hfive)

/-- The actual two independent line actions of the marked order-sixteen I. -/
def sourceTorusAction
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    sourceI e →* MulAut (B5Image B5) × MulAut (fixedFive B5 (sourceU e)) :=
  ((B5Image B5).normalizerMonoidHom.comp
      (inclusion (sourceI_le_normalizer B5 e hfive))).prod
    ((fixedFive B5 (sourceU e)).normalizerMonoidHom.comp
      (inclusion (sourceI_normalizes_fixed B5 e hfive _ (source_marks_mem c e hz).2)))

/-- The line-pair action is faithful on the original I, by self-centrality
of the same edge and its coprime order. -/
theorem sourceTorusAction_injective
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    Function.Injective (sourceTorusAction c B5 e hz hfive) := by
  obtain ⟨hu,hi⟩ := source_inverter c B5 e hz hfive
  have hd : Disjoint (sourceI e) (edge B5 (sourceU e)) :=
    disjoint_of_coprime_natCard (by
      rw [sourceI_card e,base_fixed_card c B5 (sourceU e) hu hfusion hi]
      decide)
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hB : B5Image B5≤(MulAut.conj (x:G)).toMonoidHom.eqLocus (MonoidHom.id G) := by
    intro a ha
    have he := congrArg (fun f:MulAut (B5Image B5) × MulAut (fixedFive B5 (sourceU e)) =>
      ((f.1 ⟨a,ha⟩:B5Image B5):G)) hx
    exact he
  have hA : fixedFive B5 (sourceU e)≤
      (MulAut.conj (x:G)).toMonoidHom.eqLocus (MonoidHom.id G) := by
    intro a ha
    have he := congrArg (fun f:MulAut (B5Image B5) × MulAut (fixedFive B5 (sourceU e)) =>
      ((f.2 ⟨a,ha⟩:fixedFive B5 (sourceU e)):G)) hx
    exact he
  have hE : edge B5 (sourceU e)≤
      (MulAut.conj (x:G)).toMonoidHom.eqLocus (MonoidHom.id G) := sup_le hB hA
  have hxC : (x:G)∈centralizer (edge B5 (sourceU e) : Set G) := by
    intro a ha
    have he : (x:G)*a*(x:G)⁻¹=a := hE ha
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hxE : (x:G)∈edge B5 (sourceU e) := by
    change (x:G)∈B5Image B5 ⊔ fixedFive B5 (sourceU e)
    rw [← centralizer_base_fixed c B5 (sourceU e) hu hfusion hi]
    exact hxC
  exact Subtype.ext (disjoint_def.mp hd x.property hxE)

/-- Every pair of cyclic-five automorphisms is induced by a unique actor
in the same original I. No diagonal torus image is assumed. -/
theorem sourceTorusAction_bijective
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    Function.Bijective (sourceTorusAction c B5 e hz hfive) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨hu,hi⟩ := source_inverter c B5 e hz hfive
  have hB := B5Image_card d.card_Z B5
  have hA := (source_three_fives c B5 (sourceU e) hu hfusion hi).1
  let : IsCyclic (B5Image B5) := isCyclic_of_prime_card hB
  let : IsCyclic (fixedFive B5 (sourceU e)) := isCyclic_of_prime_card hA
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨sourceTorusAction_injective c B5 e hz hfive hfusion,?_⟩
  rw [sourceI_card e,Nat.card_prod,IsCyclic.card_mulAut,IsCyclic.card_mulAut,hB,hA]
  rw [Nat.totient_prime (by decide : Nat.Prime 5)]

/-- The exact full split torus, with both original restriction maps. -/
def sourceTorusEquiv
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    sourceI e ≃* MulAut (B5Image B5) × MulAut (fixedFive B5 (sourceU e)) :=
  MulEquiv.ofBijective (sourceTorusAction c B5 e hz hfive)
    (sourceTorusAction_bijective c B5 e hz hfive hfusion)

/-- Evaluation on the actual base five-subgroup is ambient conjugation. -/
theorem sourceTorusEquiv_first
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) (i:sourceI e) (b:B5Image B5) :
    ((sourceTorusEquiv c B5 e hz hfive hfusion i).1 b:G)=(i:G)*(b:G)*(i:G)⁻¹ := rfl

/-- Evaluation on the new fixed five-subgroup is the same ambient conjugation. -/
theorem sourceTorusEquiv_second
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) (i:sourceI e) (b:fixedFive B5 (sourceU e)) :
    ((sourceTorusEquiv c B5 e hz hfive hfusion i).2 b:G)=(i:G)*(b:G)*(i:G)⁻¹ := rfl

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
