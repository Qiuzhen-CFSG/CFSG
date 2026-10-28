module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSharpSection

public import Theory.Representation.BinaryConjugationSection.InvariantPreimage
public import Theory.Representation.BinaryConjugationSection.Canonical

/-!
# Irreducibility of the original unequal-field beta section

The sharp p.165 bounds make the marked beta-center/core interval a chief
interval whenever the two field orders differ. Construct the conjugation
representation on that literal quotient, factoring through the full original
beta stabilizer modulo its two-core. Every invariant subspace pulls back to
an invariant subgroup of the original core, and the chief interval forces
that subspace to be zero or the whole section.

The section coordinates are exactly the original quotient projection. No
model action or extra irreducibility premise is used. The equal-field case
of the source theorem remains a separate obligation.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.10)(d), printed pp.164--165.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)
local notation "Pβ" => parabolic L S 1
local notation "Qβ" => Subgroup.pCoreIn 2 (parabolic L S 1)
local notation "Zβ" => Subgroup.map ι (Z F β)

/-- The unequal-field part of the original (10.10)(d) irreducibility clause,
retaining the original full beta quotient and the literal section coordinates. -/
theorem original_bTwo_unequal_beta_irreducible
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (hfields : Nat.card (K false)≠Nat.card (K true)) :
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
  let Z₁ := (Z F β).map ι
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
  rcases original_bTwo_unequal_beta_interval h hc hne hb hβu ht htne K e hK hD hfields
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
