module
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankOne
public import Theory.ElementaryAbelian.BinaryRankDifference
public import Theory.Representation.BinaryOffender.SubspaceAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.QuotientAction
import Mathlib.Tactic

/-!
# Literal subspaces, commutator images, and the source dimension balance

Every space here is obtained from an actual subgroup or quotient. `inside K X`
is X∩K inside the binary group K; `quotientSpace K N X` is its image in K/N.
The source spaces D and I are Dγ and Uγ∩UH inside Uγ. Their dimension balance
comes from the F.9 kernel identity for the star map. Relative normalization
bounds the action differences on VH/UH by the image of Dγ, whose dimension is
at most dim(D/I). No ambient normality or displacement bound is assumed.

Equality of commutator images lifts to a subgroup containment modulo V₁.
A rank-two quotient together with the order-two line gives the intersection
codimension bound, which is transported through the two actual conjugators.
`Uone` fixes the notation for the full preimage of C_{ŨH}(H), with its quotient
image proved to be exactly that fixed space. The marked natural/augmentation
calculation identifying its product with V₃ is a separate obligation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 13.8.34, printed p.968 (PDF p.985), using
F.9.13 and the earlier local kernel and normalization conclusions.
-/

@[expose] public section
open Subgroup Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance

variable {G : Type*} [Group G]

/-- The binary subspace corresponding to an intrinsic elementary abelian subgroup. -/
abbrev binarySpace {K : Type*} [Group K] [IsElementaryAbelian 2 K] :
    Subgroup K ≃o Submodule (ZMod 2) (Additive K) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

/-- The literal intersection X ∩ K, regarded as a binary subspace of K. -/
abbrev inside (K X : Subgroup G) [IsElementaryAbelian 2 K] :
    Submodule (ZMod 2) (Additive K) := binarySpace (X.subgroupOf K)

theorem finrank_binarySpace {K : Type*} [Group K] [Finite K]
    [IsElementaryAbelian 2 K] (X : Subgroup K) :
    finrank (ZMod 2) (binarySpace X) = Nat.log 2 (Nat.card X) := by
  have hc : Nat.card X = 2 ^ finrank (ZMod 2) (binarySpace X) := by
    change Nat.card (binarySpace X) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hc, Nat.log_pow Nat.one_lt_two]

theorem finrank_additive {K : Type*} [Group K] [Finite K]
    [IsElementaryAbelian 2 K] :
    finrank (ZMod 2) (Additive K) = Nat.log 2 (Nat.card K) := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive K)
  change Nat.card K = _ at hc
  rw [Nat.card_zmod] at hc
  rw [hc, Nat.log_pow Nat.one_lt_two]

theorem finrank_inside [Finite G] (K X : Subgroup G) [IsElementaryAbelian 2 K]
    (hX : X ≤ K) : finrank (ZMod 2) (inside K X) = Nat.log 2 (Nat.card X) := by
  rw [finrank_binarySpace, Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv]

theorem finrank_quotient_inside [Finite G] (K X : Subgroup G)
    [IsElementaryAbelian 2 K] (hX : X ≤ K) :
    finrank (ZMod 2) (Additive K ⧸ inside K X) = Nat.log 2 (X.relIndex K) := by
  have hd := (inside K X).finrank_quotient_add_finrank
  rw [finrank_inside K X hX, finrank_additive] at hd
  rw [← log_card_sub_log_card_eq_log_relIndex K X hX]
  omega

/-- The source intersection I = Uγ ∩ UH lies in its literal commutator kernel. -/
theorem intersection_le_Dgamma (UH Uγ V₁ : Subgroup G)
    [IsElementaryAbelian 2 UH] : Uγ ⊓ UH ≤ Source.Dgamma Uγ UH V₁ := by
  apply le_commutatorPreimage inf_le_left
  have hc : ⁅Uγ ⊓ UH, UH⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (inf_le_right.trans UH.le_centralizer)
  exact hc.le.trans bot_le

/-- The two actual submodules used in the displayed source dimension balance. -/
abbrev Dspace (UH Uγ V₁ : Subgroup G) [IsElementaryAbelian 2 Uγ] :=
  inside Uγ (Source.Dgamma Uγ UH V₁)

abbrev Ispace (UH Uγ : Subgroup G) [IsElementaryAbelian 2 Uγ] :=
  inside Uγ (Uγ ⊓ UH)

theorem Ispace_le_Dspace (UH Uγ V₁ : Subgroup G)
    [IsElementaryAbelian 2 UH] [IsElementaryAbelian 2 Uγ] :
    Ispace UH Uγ ≤ Dspace UH Uγ V₁ :=
  binarySpace.monotone (subgroupOf_mono Uγ (intersection_le_Dgamma UH Uγ V₁))

/-- Rank-nullity for the source star map, with its F.9 kernel identity retained. -/
theorem dimension_balance [Finite G] (H UH Uγ V₁ : Subgroup G)
    [IsElementaryAbelian 2 Uγ] (hγH : Uγ ≤ H)
    (hkernel : Source.Dgamma Uγ UH V₁ = Uγ ⊓ Source.QH H) :
    finrank (ZMod 2) (Dspace UH Uγ V₁) +
      Representation.BinaryOffender.rank (Source.starImage H Uγ) =
        finrank (ZMod 2) (Additive Uγ) := by
  have hd := (Dspace UH Uγ V₁).finrank_quotient_add_finrank
  rw [finrank_quotient_inside Uγ (Source.Dgamma Uγ UH V₁) (commutatorPreimage_le _ _ _),
    hkernel, inf_relIndex_left, ← CriticalGeometry.starImage_card H Uγ hγH] at hd
  exact (Nat.add_comm _ _).trans hd

/-- Conjugation identifies the sizes of UH and Uγ in the source equation. -/
theorem dimension_conjugate [Finite G] (UH Uγ : Subgroup G)
    [IsElementaryAbelian 2 UH] [IsElementaryAbelian 2 Uγ]
    (g : G) (hg : UH.map (MulAut.conj g).toMonoidHom = Uγ) :
    finrank (ZMod 2) (Additive UH) = finrank (ZMod 2) (Additive Uγ) := by
  rw [finrank_additive, finrank_additive, ← hg,
    card_map_of_injective (MulAut.conj g).injective]

/-- The relative quotient Dγ/(Dγ ∩ UH) is exactly the source D/I dimension. -/
theorem Dspace_quotient_finrank [Finite G] (UH Uγ V₁ : Subgroup G)
    [IsElementaryAbelian 2 UH] [IsElementaryAbelian 2 Uγ] :
    finrank (ZMod 2) (Dspace UH Uγ V₁ ⧸
      (Ispace UH Uγ).comap (Dspace UH Uγ V₁).subtype) =
        Nat.log 2 (UH.relIndex (Source.Dgamma Uγ UH V₁)) := by
  let D := Source.Dgamma Uγ UH V₁
  let I := Uγ ⊓ UH
  have hD : D ≤ Uγ := commutatorPreimage_le _ _ _
  have hI : I ≤ D := intersection_le_Dgamma UH Uγ V₁
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le hD
  have he : D ⊓ UH = I := le_antisymm
    (inf_le_inf_right UH hD) (le_inf hI inf_le_right)
  have hd := ((Ispace UH Uγ).comap (Dspace UH Uγ V₁).subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe (Ispace_le_Dspace UH Uγ V₁)).finrank_eq,
    finrank_inside Uγ _ inf_le_left, finrank_inside Uγ _ hD] at hd
  rw [← inf_relIndex_left D UH, he,
    ← log_card_sub_log_card_eq_log_relIndex D I hI]
  dsimp only [I, D] at *
  omega


/-- The image of X in the literal quotient K/N, as a binary subspace. -/
abbrev quotientSpace (K N X : Subgroup G) [IsElementaryAbelian 2 K] :
    Submodule (ZMod 2) (Additive (K ⧸ N.subgroupOf K)) :=
  binarySpace (SolvableExclusion.tildeImage K N X)

theorem finrank_quotientSpace [Finite G] (K N X : Subgroup G)
    [IsElementaryAbelian 2 K] :
    finrank (ZMod 2) (quotientSpace K N X) = Nat.log 2 (N.relIndex (X ⊓ K)) := by
  rw [finrank_binarySpace]
  change Nat.log 2 (Nat.card ((X.subgroupOf K).map (QuotientGroup.mk' _))) = _
  rw [← relIndex_ker, QuotientGroup.ker_mk',
    ← inf_subgroupOf_right X K, relIndex_subgroupOf inf_le_right]

/-- The image of a subgroup in K/N has dimension at most its index modulo N,
even if the subgroup is not contained in K. -/
theorem finrank_quotientSpace_le [Finite G] (K N X : Subgroup G)
    [IsElementaryAbelian 2 K] :
    finrank (ZMod 2) (quotientSpace K N X) ≤ Nat.log 2 (N.relIndex X) := by
  rw [finrank_quotientSpace]
  exact Nat.log_mono_right (relIndex_le_of_le_right inf_le_left
    (N.subgroupOf X).index_ne_zero_of_finite)

/-- Conjugation on the actual section puts every action difference in the
image of the ambient commutator subgroup. -/
theorem section_commutator_le (H V V₃ X : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hρ : SectionConjugation H V V₃ ρ) (B : Subgroup G)
    (hcomm : ⁅Source.VH H V, B⁆ ≤ X) :
    Representation.BinaryOffender.subspaceCommutator ρ ⊤ (Source.starImage H B) ≤
      quotientSpace (Source.VH H V) (Source.UH H V₃) X := by
  apply Submodule.span_le.mpr
  rintro _ ⟨b, ⟨h, hh, rfl⟩, v, _, rfl⟩
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((Source.UH H V₃).subgroupOf (Source.VH H V)) v.toMul
  change QuotientGroup.mk' _ x = v.toMul at hx
  have hv : Additive.ofMul (QuotientGroup.mk' _ x) = v := congrArg Additive.ofMul hx
  rw [← hv, hρ]
  change (QuotientGroup.mk' _ _) / (QuotientGroup.mk' _ x) ∈
    SolvableExclusion.tildeImage (Source.VH H V) (Source.UH H V₃) X
  rw [← map_div]
  apply mem_map_of_mem
  change ((h : G) * (x : G) * (h : G)⁻¹) / (x : G) ∈ X
  rw [commutator_comm] at hcomm
  simpa only [commutatorElement_def, div_eq_mul_inv, coe_subtype] using
    hcomm (commutator_mem_commutator hh x.property)

/-- The source commutator bound follows from mutual normalization and the
F.9 kernel identity. No displacement-dimension bound is assumed. -/
theorem source_commutator_le_Dgamma (H V V₃ Uγ V₁ : Subgroup G)
    (hγH : Uγ ≤ H)
    (hn : Source.VH H V ≤ normalizer (Uγ : Set G))
    (hVQ : Source.VH H V ≤ Source.QH H)
    (hkernel : Source.Dgamma Uγ (Source.UH H V₃) V₁ = Uγ ⊓ Source.QH H) :
    ⁅Source.VH H V, Uγ⁆ ≤ Source.Dgamma Uγ (Source.UH H V₃) V₁ := by
  rw [hkernel]
  exact le_inf (le_normalizer_iff_commutator_le_right.mp hn)
    ((le_normalizer_iff_commutator_le_left.mp
      (hγH.trans (le_normalizer_conjugateSpanBy V H))).trans hVQ)

/-- The displacement bound in the displayed source equation, on VH/UH and
with the denominator the actual intersection I in the actual Dγ. -/
theorem source_displacement_bound [Finite G] (H V V₃ Uγ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 Uγ]
    (hγH : Uγ ≤ H) (hn : Source.VH H V ≤ normalizer (Uγ : Set G))
    (hVQ : Source.VH H V ≤ Source.QH H)
    (hkernel : Source.Dgamma Uγ (Source.UH H V₃) V₁ = Uγ ⊓ Source.QH H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hρ : SectionConjugation H V V₃ ρ) :
    finrank (ZMod 2) (Representation.BinaryOffender.subspaceCommutator ρ ⊤
      (Source.starImage H Uγ)) ≤
    finrank (ZMod 2) (Dspace (Source.UH H V₃) Uγ V₁ ⧸
      (Ispace (Source.UH H V₃) Uγ).comap (Dspace (Source.UH H V₃) Uγ V₁).subtype) := by
  rw [Dspace_quotient_finrank]
  exact (Submodule.finrank_mono (section_commutator_le H V V₃ _ ρ hρ Uγ
    (source_commutator_le_Dgamma H V V₃ Uγ V₁ hγH hn hVQ hkernel))).trans
      (finrank_quotientSpace_le _ _ _)


/-- Lifting a displacement into UαV₁ loses at most the one-dimensional
line V₁. This is the codimension-three inference, before conjugating α to γ. -/
theorem intersection_codimension_le_three [Finite G] (UH Uα V₁ K : Subgroup G)
    [IsElementaryAbelian 2 UH]
    (hV : V₁ ≤ UH) (hK : K ≤ UH) (hn : Uα ≤ normalizer (V₁ : Set G))
    (hlift : K ≤ Uα ⊔ V₁) (hline : Nat.card V₁ = 2)
    (hdim : finrank (ZMod 2) (Additive UH ⧸ inside UH K) = 2) :
    finrank (ZMod 2) (Additive UH ⧸ inside UH (UH ⊓ Uα)) ≤ 3 := by
  have hle : K ≤ (UH ⊓ Uα) ⊔ V₁ := by
    intro k hk
    have hm := hlift hk
    change k ∈ ((Uα ⊔ V₁ : Subgroup G) : Set G) at hm
    rw [coe_mul_of_left_le_normalizer_right Uα V₁ hn] at hm
    obtain ⟨a, ha, z, hz, rfl⟩ := hm
    have haU : a ∈ UH := by
      have ht := UH.mul_mem (hK hk) (UH.inv_mem (hV hz))
      simpa only [mul_inv_cancel_right] using ht
    exact ((UH ⊓ Uα) ⊔ V₁).mul_mem (mem_sup_left ⟨haU, ha⟩) (mem_sup_right hz)
  have hsub : inside UH K ≤ inside UH (UH ⊓ Uα) ⊔ inside UH V₁ := by
    have hh := binarySpace.monotone (subgroupOf_mono UH hle)
    rwa [subgroupOf_sup inf_le_left hV, (binarySpace (K := UH)).map_sup] at hh
  have hbound := Submodule.finrank_mono hsub
  have hs := (inside UH (UH ⊓ Uα)).finrank_sup_add_finrank_inf_eq (inside UH V₁)
  have hk := (inside UH K).finrank_quotient_add_finrank
  have hi := (inside UH (UH ⊓ Uα)).finrank_quotient_add_finrank
  have hz : finrank (ZMod 2) (inside UH V₁) = 1 := by
    rw [finrank_inside UH V₁ hV, hline]; decide
  omega

/-- The γ-to-α conjugator in H preserves UH and therefore preserves the
codimension of its intersection with these actual conjugate subgroups. -/
theorem alpha_gamma_intersection_codimension [Finite G]
    (H V₃ Uα Uγ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (h : H) (hconj : Uγ.map (MulAut.conj (h : G)).toMonoidHom = Uα) :
    finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸ inside (Source.UH H V₃)
      (Source.UH H V₃ ⊓ Uγ)) =
    finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸ inside (Source.UH H V₃)
      (Source.UH H V₃ ⊓ Uα)) := by
  have hU : (Source.UH H V₃).map (MulAut.conj (h : G)).toMonoidHom = Source.UH H V₃ :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy V₃ H h.property)
  rw [finrank_quotient_inside _ _ inf_le_left,
    finrank_quotient_inside _ _ inf_le_left, inf_relIndex_left, inf_relIndex_left]
  congr 1
  have he := relIndex_map_map (MulAut.conj (h : G)).toMonoidHom Uγ (Source.UH H V₃)
  rw [hconj, hU, (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj (h : G)).injective,
    sup_bot_eq, sup_bot_eq] at he
  exact he.symm

/-- The critical-pair conjugator identifies UH and Uγ, converting the bound
inside UH into the bound on the literal quotient Uγ/(Uγ∩UH). -/
theorem gamma_codimension_eq [Finite G] (UH Uγ : Subgroup G)
    [IsElementaryAbelian 2 UH] [IsElementaryAbelian 2 Uγ]
    (g : G) (hg : UH.map (MulAut.conj g).toMonoidHom = Uγ) :
    finrank (ZMod 2) (Additive Uγ ⧸ Ispace UH Uγ) =
      finrank (ZMod 2) (Additive UH ⧸ inside UH (UH ⊓ Uγ)) := by
  have hdim := dimension_conjugate UH Uγ g hg
  have hγ := (Ispace UH Uγ).finrank_quotient_add_finrank
  have hH := (inside UH (UH ⊓ Uγ)).finrank_quotient_add_finrank
  rw [finrank_inside Uγ _ inf_le_left] at hγ
  rw [finrank_inside UH _ inf_le_left, inf_comm UH Uγ] at hH
  rw [inf_comm UH Uγ]
  omega


/-- Recover a genuine subgroup containment from the image in UH/V₁. -/
theorem le_sup_of_quotientSpace_le (UH V₁ X Y : Subgroup G)
    [IsElementaryAbelian 2 UH] (hX : X ≤ UH)
    (himage : quotientSpace UH V₁ X ≤ quotientSpace UH V₁ Y) : X ≤ Y ⊔ V₁ := by
  intro x hx
  have hm : Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf UH) ⟨x, hX hx⟩) ∈
      quotientSpace UH V₁ Y := himage ⟨⟨x, hX hx⟩, hx, rfl⟩
  obtain ⟨y, hy, he⟩ := hm
  have hz : x / (y : G) ∈ V₁ := by
    have hq : QuotientGroup.mk' (V₁.subgroupOf UH) ⟨x, hX hx⟩ =
        QuotientGroup.mk' (V₁.subgroupOf UH) y := he.symm
    have hz' : (⟨x, hX hx⟩ : UH) / y ∈ V₁.subgroupOf UH :=
      QuotientGroup.eq_iff_div_mem.mp hq
    exact hz'
  have ht := (Y ⊔ V₁).mul_mem (mem_sup_right hz) (mem_sup_left hy)
  simpa only [coe_subtype, div_mul_cancel] using ht

/-- The actual commutator image lifts into UαV₁ using the normalization
UH ≤ N_G(Uα) from F.9.13. -/
theorem lift_displacement (UH Uα V₁ K : Subgroup G)
    [IsElementaryAbelian 2 UH] (hK : K ≤ UH)
    (hn : UH ≤ normalizer (Uα : Set G))
    (himage : quotientSpace UH V₁ K = quotientSpace UH V₁ ⁅UH, Uα⁆) :
    K ≤ Uα ⊔ V₁ := by
  exact (le_sup_of_quotientSpace_le UH V₁ K ⁅UH, Uα⁆ hK himage.le).trans
    (sup_le_sup_right (le_normalizer_iff_commutator_le_right.mp hn) V₁)

/-- Binary linearization of the actual action on UH/V₁. -/
def tildeRepresentation (H UH V₁ : Subgroup G) [IsElementaryAbelian 2 UH]
    (a : SolvableExclusion.Five.StarAction H UH V₁) :
    Representation (ZMod 2) (Source.Hstar H) (Additive (UH ⧸ V₁.subgroupOf UH)) where
  toFun g := (CriticalGeometry.binaryLinear (a.action g)).toLinearMap
  map_one' := by
    ext x
    change Additive.ofMul (a.action 1 x.toMul) = x
    rw [map_one]; rfl
  map_mul' g h := by
    ext x
    change Additive.ofMul (a.action (g * h) x.toMul) =
      Additive.ofMul (a.action g (a.action h x.toMul))
    rw [map_mul]; rfl

/-- U₁ is chosen as the full preimage of C_{ŨH}(H). Thus V₁≤U₁ and the
notation Ũ₁ denotes exactly the source fixed space, in both module branches. -/
noncomputable def Uone (H UH V₁ : Subgroup G) [IsElementaryAbelian 2 UH]
    (a : SolvableExclusion.Five.StarAction H UH V₁) : Subgroup G :=
  (((tildeRepresentation H UH V₁ a).invariants.toAddSubgroup.toSubgroup').comap
    (QuotientGroup.mk' (V₁.subgroupOf UH))).map UH.subtype

theorem Uone_le (H UH V₁ : Subgroup G) [IsElementaryAbelian 2 UH]
    (a : SolvableExclusion.Five.StarAction H UH V₁) : Uone H UH V₁ a ≤ UH :=
  map_subtype_le _

theorem line_le_Uone (H UH V₁ : Subgroup G) [IsElementaryAbelian 2 UH]
    (a : SolvableExclusion.Five.StarAction H UH V₁) (hV : V₁ ≤ UH) :
    V₁ ≤ Uone H UH V₁ a := by
  intro v hv
  refine ⟨⟨v, hV hv⟩, ?_, rfl⟩
  change Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf UH) ⟨v, hV hv⟩) ∈
    (tildeRepresentation H UH V₁ a).invariants
  have he : QuotientGroup.mk' (V₁.subgroupOf UH) ⟨v, hV hv⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hv
  rw [he]
  exact Submodule.zero_mem _

/-- The quotient image of the chosen U₁ is precisely the fixed space. -/
theorem quotientSpace_Uone (H UH V₁ : Subgroup G) [IsElementaryAbelian 2 UH]
    (a : SolvableExclusion.Five.StarAction H UH V₁) :
    quotientSpace UH V₁ (Uone H UH V₁ a) = (tildeRepresentation H UH V₁ a).invariants := by
  unfold quotientSpace SolvableExclusion.tildeImage Uone
  change binarySpace ((((((tildeRepresentation H UH V₁ a).invariants.toAddSubgroup.toSubgroup').comap
    (QuotientGroup.mk' (V₁.subgroupOf UH))).map UH.subtype).comap UH.subtype).map
      (QuotientGroup.mk' (V₁.subgroupOf UH))) = _
  rw [comap_map_eq_self_of_injective UH.subtype_injective,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  rfl

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance
