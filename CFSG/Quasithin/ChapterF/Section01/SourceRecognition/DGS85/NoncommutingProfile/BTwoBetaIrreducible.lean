module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSecondKernel
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage
public import Theory.Representation.BinaryConjugationSection.Canonical

/-!
# The full nonbinary beta irreducibility clause

A proper invariant section produces the abelian supplement from p.165.
Its second-kernel bound supplies a new invariant section strictly above
Z_beta and below Q_beta, but contained in Q_alpha. This contradicts the
proved escape of every such section from Q_alpha, including equal fields.

The resulting chief interval gives an irreducible representation on the
literal quotient Q_beta/Z_beta. Its action factors through the full
original beta stabilizer modulo its two-core, and its coordinates are the
original quotient projection. No field inequality remains as an assumption.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.10)(d), printed pp.164--165.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting
open DGS85.Reduction CommutingOneProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The p.165 second-kernel contradiction excludes every proper nonzero
beta-invariant section, including equal fields. -/
theorem original_bTwo_nonbinary_beta_no_proper_section
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆≠⊥)
    (hb : b F₀=2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map ι≠(Z F₀ α).map ι)
    (N : Subgroup G) (hNQ : N<(parabolic L S 1).pCoreIn 2)
    (hZN : (Z F₀ β).map ι<N) (hPN : parabolic L S 1≤normalizer (N:Set G)) : False := by
  let H := reduced_triple h
  let _ : ∀ i, Finite (F₀ i) := finite_endpoints H
  have hab : (graph F₀).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨heq,_,_,_,hescape⟩ := original_bTwo_nonbinary_beta_proper_core_intersection
    h hc hne hb hβu ht htne K e hK hD N hNQ hZN hPN
  obtain ⟨g,hg,hgt,hdis,hpair,habel,hcard,hint,hsup,hnorm⟩ :=
    original_bTwo_proper_section_abelian_supplement h hc hne hb hβu ht htne K e hK hD N hNQ hZN hPN
  let W := (N⊓(parabolic L S 0).pCoreIn 2)⊔
    ((N.map (MulAut.conj (g:G)).toMonoidHom)⊓(parabolic L S 0).pCoreIn 2)
  change IsMulCommutative W at habel
  let _ := habel
  have hlower := original_abelian_supplement_second_core_bound h hc hne hb hβu ht htne
    K e hD heq W hcard hsup
  let I := neighborCoreIntersection F₀ β
  let I₀ := I.map ι
  have hQa : (Q F₀ α).map ι=(parabolic L S 0).pCoreIn 2 := reduced_base_Q_map h false
  have hQb : (Q F₀ β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
  have hIQa : I₀≤(parabolic L S 0).pCoreIn 2 := by
    rw [←hQa]
    exact map_mono (neighborCoreIntersection_le F₀ hab)
  have hIQb : I₀≤(parabolic L S 1).pCoreIn 2 := by
    rw [←hQb]
    exact map_mono (source_neighborCoreIntersection_le_core H hab)
  have hIQlt : I₀<(parabolic L S 1).pCoreIn 2 := lt_of_le_of_ne hIQb (by
    intro he
    exact hescape (hNQ.le.trans (he ▸ hIQa)))
  have hZI : Z F₀ β≤I := by
    apply le_iInf
    intro z
    exact graph_Z_le_Q_of_short H (reduced_kernel_sylow h) (by
      change (graph F₀).dist β z < b F₀
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr z.property,hb]
      decide)
  have hZI₀ : (Z F₀ β).map ι≤I₀ := map_mono hZI
  have hZcard : Nat.card ((Z F₀ β).map ι)=Nat.card (K true) := by
    obtain ⟨_,_,_,_,hh,_⟩ := original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD
    exact hh.trans heq
  have hIcard : Nat.card (K true)^2≤Nat.card I₀ := by
    rw [←reduced_neighborCoreIntersection_eq_second_core h hab] at hlower
    rw [card_map_of_injective (G₀ L S).subtype_injective]
    exact hlower
  have hZIlt : (Z F₀ β).map ι<I₀ := lt_of_le_of_ne hZI₀ (by
    intro he
    rw [←he,hZcard] at hIcard
    nlinarith only [hK,hIcard])
  have hh := original_bTwo_nonbinary_beta_proper_core_intersection h hc hne hb hβu ht htne
    K e hK hD I₀ hIQlt hZIlt (original_second_core_normalized h)
  exact hh.2.2.2.2 hIQa

/-- The full original beta stabilizer acts on a chief center/core interval
in every nonbinary-beta strict branch. -/
theorem original_bTwo_nonbinary_beta_interval
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆≠⊥)
    (hb : b F₀=2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map ι≠(Z F₀ α).map ι)
    (N : Subgroup G) (hNQ : N≤(parabolic L S 1).pCoreIn 2)
    (hZN : (Z F₀ β).map ι≤N) (hPN : parabolic L S 1≤normalizer (N:Set G)) :
    N=(Z F₀ β).map ι ∨ N=(parabolic L S 1).pCoreIn 2 := by
  by_cases hz : N=(Z F₀ β).map ι
  · exact Or.inl hz
  by_cases hq : N=(parabolic L S 1).pCoreIn 2
  · exact Or.inr hq
  exact (original_bTwo_nonbinary_beta_no_proper_section h hc hne hb hβu ht htne K e hK hD
    N (lt_of_le_of_ne hNQ hq) (lt_of_le_of_ne hZN (Ne.symm hz)) hPN).elim

local notation "Pβ" => parabolic L S 1
local notation "Qβ" => Subgroup.pCoreIn 2 (parabolic L S 1)
local notation "Zβ" => Subgroup.map ι (Z F₀ β)

/-- The nonbinary-beta clause of DGS (10.10)(d), on the literal original
core quotient with the action of the full original stabilizer quotient. -/
theorem original_bTwo_nonbinary_beta_irreducible
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆≠⊥)
    (hb : b F₀=2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F₀ t).map ι≠(Z F₀ α).map ι) :
    ∃ hN : ((Zβ).subgroupOf Qβ).Normal, letI := hN
      ∃ hel : IsElementaryAbelian 2 (Qβ⧸(Zβ).subgroupOf Qβ), letI := hel
        ∃ ρ : Representation (ZMod 2) (Pβ⧸pCore 2 Pβ) (Additive (Qβ⧸(Zβ).subgroupOf Qβ)),
          ∃ d : Representation.BinaryConjugationSection Pβ Qβ Zβ
              (ρ.comp (QuotientGroup.mk' (pCore 2 Pβ))),
            (∀ q : Qβ, (d.coordinates q).toAdd =
              Additive.ofMul (QuotientGroup.mk' ((Zβ).subgroupOf Qβ) q)) ∧
            ρ.IsIrreducible ∧
            Nat.card (Qβ⧸(Zβ).subgroupOf Qβ)=Nat.card (K false)^2*Nat.card (K true)^2 := by
  let P := parabolic L S 1
  let Q₁ := P.pCoreIn 2
  let Z₁ := (Z F₀ β).map ι
  have hPQ : P≤normalizer (Q₁:Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hPhi,hder⟩ :=
    original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD
  change (frattini Q₁).map Q₁.subtype=Z₁ at hPhi
  change ⁅Q₁,Q₁⁆=Z₁ at hder
  have hPZ : P≤normalizer (Z₁:Set G) := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,←hder,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hPQ ha)]
  have hQP : Q₁≤P := pCoreIn_le 2 P
  let := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion hQP) (inclusion_injective _)
  let hN : (Z₁.subgroupOf Q₁).Normal := normal_subgroupOf_of_le_normalizer (hQP.trans hPZ)
  let _ := hN
  have hel : IsElementaryAbelian 2 (Q₁⧸Z₁.subgroupOf Q₁) :=
    elementary_quotient_of_frattini_le (isPGroup_pCoreIn 2 P) _
      (map_le_iff_le_comap.mp hPhi.le)
  let _ := hel
  obtain ⟨hZQ,htotal⟩ := original_bTwo_strict_beta_total_section h hc hne hb hβu ht htne K e hD
  change Z₁<Q₁ at hZQ
  change Nat.card (Q₁⧸Z₁.subgroupOf Q₁)=Nat.card (K false)^2*Nat.card (K true)^2 at htotal
  let : Nontrivial (Q₁⧸Z₁.subgroupOf Q₁) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [htotal]
    have ha : 1<Nat.card (K false)^2 := one_lt_pow₀ Finite.one_lt_card (by decide)
    exact lt_of_lt_of_le ha (Nat.le_mul_of_pos_right _ (Nat.pow_pos Nat.card_pos)))
  let π := QuotientGroup.mk' (pCore 2 P)
  have hk : π.ker=Q₁.subgroupOf P := by
    rw [QuotientGroup.ker_mk']
    exact (comap_map_eq_self_of_injective P.subtype_injective _).symm
  obtain ⟨ρ,d,hd⟩ := Representation.BinaryConjugationSection.exists_canonical
    P Q₁ Z₁ hQP hZQ.le hPQ hPZ π (QuotientGroup.mk'_surjective _) hk
  refine ⟨hN,hel,ρ,d,hd,?_,htotal⟩
  apply (Representation.irreducible_comp_surjective_iff π (QuotientGroup.mk'_surjective _) ρ).mp
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨⟨⟨⊥,⊤,?_⟩⟩,?_⟩
  · intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  intro W
  rcases original_bTwo_nonbinary_beta_interval h hc hne hb hβu ht htne K e hK hD
      (d.invariantPreimage W) (d.invariantPreimage_le W)
      (d.kernel_le_invariantPreimage W) (d.invariantPreimage_normalized W) with hz | hq
  · left
    change d.invariantPreimage W=Z₁ at hz
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro w hw
    obtain ⟨q,hqw⟩ := d.onto (Multiplicative.ofAdd w)
    have hm : (q:G)∈d.invariantPreimage W :=
      (d.mem_invariantPreimage W q).mpr ⟨q.property,by simpa only [hqw,toAdd_ofAdd] using hw⟩
    have hzero := (d.coordinates_eq_one_iff q).mpr (hz ▸ hm)
    change w=0
    exact congrArg Multiplicative.toAdd (hqw.symm.trans hzero)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    obtain ⟨q,hqw⟩ := d.onto (Multiplicative.ofAdd w)
    have hm : (q:G)∈d.invariantPreimage W := hq.symm ▸ q.property
    obtain ⟨_,hw⟩ := (d.mem_invariantPreimage W q).mp hm
    simpa only [hqw,toAdd_ofAdd] using hw

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
