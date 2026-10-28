module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCoreSplitting
public import Theory.Representation.NormalInvariants

/-!
# Normalizers of complements in the original eight-field endpoint

Irreducibility of the actual core quotient makes its complement fixed space
zero. Hence a full-core complement centralizes exactly the original central
line in the core. The normalizer of that same complement in the original
endpoint is its join with that line. This retains the full core and literal
complement for the subsequent reflection-actor comparison.
-/

noncomputable section
open Subgroup Theory.GroupTheory Representation Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceComplementNormalizer

private theorem invariants_bot_of_degree_eight
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [ρ.IsIrreducible]
    (hd : finrank (ZMod 2) V = 8) : ρ.invariants = ⊥ := by
  by_contra hn
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  let W : Subrepresentation ρ := {
    toSubmodule := Submodule.span (ZMod 2) {v}
    apply_mem_toSubmodule := by
      intro g w hw
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul,hv g]
      exact Submodule.smul_mem _ a (Submodule.subset_span rfl) }
  have hnW : W ≠ ⊥ := by
    intro hh
    have hm : v ∈ W := Submodule.subset_span rfl
    rw [hh] at hm
    exact hv0 hm
  have ht : W = ⊤ := (eq_bot_or_eq_top W).resolve_left hnW
  have hsub : W.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule ht
  have hdim : finrank (ZMod 2) W.toSubmodule = 1 := finrank_span_singleton hv0
  rw [hsub,finrank_top,hd] at hdim
  contradiction

private theorem normalizer_complement
    {D : Type*} [Group D] (N K : Subgroup D) [N.Normal]
    (h : N.IsComplement' K) :
    normalizer (K : Set D) = K ⊔ (N ⊓ centralizer (K : Set D)) := by
  have hi : N ⊓ normalizer (K : Set D) ≤ centralizer (K : Set D) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply h.disjoint.le_bot.trans' (le_inf ?_ ?_)
    · exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (show K ≤ normalizer (N : Set D) from
          le_normalizer_of_normal))
    · exact le_normalizer_iff_commutator_le_right.mp inf_le_right
  apply le_antisymm
  · intro x hx
    obtain ⟨⟨n,k⟩,he⟩ := h.2 x
    have hn : (n : D) ∈ normalizer (K : Set D) := by
      have he' : (n : D) = x * (k : D)⁻¹ := eq_mul_inv_of_mul_eq he
      rw [he']
      exact (normalizer (K : Set D)).mul_mem hx
        ((normalizer (K : Set D)).inv_mem (K.le_normalizer k.property))
    rw [←he]
    exact (K ⊔ (N ⊓ centralizer (K : Set D))).mul_mem
      ((show N ⊓ centralizer (K : Set D) ≤ K ⊔ (N ⊓ centralizer (K : Set D)) from
        le_sup_right) ⟨n.property,hi ⟨n.property,hn⟩⟩)
      ((show K ≤ K ⊔ (N ⊓ centralizer (K : Set D)) from le_sup_left) k.property)
  · exact sup_le K.le_normalizer (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_centralizer_of_structure (P : Subgroup G)
    (hs : HasIrreducibleExtraspecialCore P)
    (K : Subgroup P) (hK : (pCore 2 P).IsComplement' K) :
    pCore 2 P ⊓ centralizer (K : Set P) = (centerIn (P.pCoreIn 2)).subgroupOf P := by
  obtain ⟨hex,Z,hZ,hN,hel,ρ,d,hcoord,hirr,hcard⟩ := hs
  let _ := hN
  let _ := hel
  let _ := hirr
  let _ := hex
  let Q := P.pCoreIn 2
  let V := Additive (Q ⧸ Z.subgroupOf Q)
  let : Finite V := Nat.finite_of_card_ne_zero (by
    change Nat.card (Q ⧸ Z.subgroupOf Q) ≠ 0
    rw [hcard]
    decide)
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hd : finrank (ZMod 2) V = 8 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) (hc.symm.trans hcard :
      2 ^ finrank (ZMod 2) V = 2 ^ 8)
  have hfix := invariants_bot_of_degree_eight ρ hd
  have hz2 : Nat.card (centerIn Q) = 2 := by
    rw [centerIn_eq_map_center,card_map_of_injective Q.subtype_injective]
    exact IsExtraspecial.center_order_p 2 Q
  have hzC : centerIn Q ≤ centralizer (P : Set G) :=
    centerIn_centralizes_of_card_two hz2 d.normalized
  ext x
  constructor
  · rintro ⟨hx,hxK⟩
    let u : Q := ⟨x,⟨x,hx,rfl⟩⟩
    have hv : (d.coordinates u).toAdd ∈ ρ.invariants := by
      intro g
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P) g
      obtain ⟨⟨n,k⟩,he⟩ := hK.2 a
      have hq : QuotientGroup.mk' (pCore 2 P) a =
          QuotientGroup.mk' (pCore 2 P) (k : P) := by
        have hn : QuotientGroup.mk' (pCore 2 P) (n:P) = 1 :=
          (QuotientGroup.eq_one_iff (n:P)).mpr n.property
        rw [←he,map_mul]
        change QuotientGroup.mk' (pCore 2 P) (n:P) *
          QuotientGroup.mk' (pCore 2 P) (k:P) = _
        rw [hn,one_mul]
      rw [hq]
      have hc : (k : G) * x * (k : G)⁻¹ = x := by
        have hh : (k : P) * x = x * k := hxK k k.property
        have hh' := congrArg (fun p : P => (p : G)) hh
        simpa only [coe_mul,mul_inv_cancel_right] using congrArg (fun z => z*(k:G)⁻¹) hh'
      have hh := d.equivariant (k : P) u
      have hu : (⟨(k:G)*u*(k:G)⁻¹,
          (mem_normalizer_iff.mp (d.normalized (k:P).property) u).mp u.property⟩ : Q) = u :=
        Subtype.ext hc
      rw [hu] at hh
      exact hh.symm
    have hv0 : (d.coordinates u).toAdd = 0 := by
      simpa only [hfix,Submodule.mem_bot] using hv
    have huZ : (x : G) ∈ Z := (d.coordinates_eq_one_iff u).mp hv0
    rwa [hZ] at huZ
  · intro hx
    refine ⟨?_,?_⟩
    · have hxQ : (x : G) ∈ Q := (show centerIn Q ≤ Q from inf_le_left) hx
      obtain ⟨y,hy,he⟩ := hxQ
      exact (Subtype.ext he : y = x) ▸ hy
    · intro k hk
      exact Subtype.ext (hzC hx k k.property)

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- In the original endpoint, every full-core complement has exactly the
original central line as its core centralizer and as its normalizer excess. -/
public theorem source_complement_normalizer (K : Subgroup H)
    (hK : (pCore 2 H).IsComplement' K) :
    let Z := (centerIn (H.pCoreIn 2)).subgroupOf H
    pCore 2 H ⊓ centralizer (K : Set H) = Z ∧
      normalizer (K : Set H) = K ⊔ Z := by
  have hc := core_centralizer_of_structure H
    (source_core_structure hG T hempty hM hu hmany hcard e H hH eR) K hK
  exact ⟨hc,(normalizer_complement (pCore 2 H) K hK).trans (congrArg (K ⊔ ·) hc)⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceComplementNormalizer
