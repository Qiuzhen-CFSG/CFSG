module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveSeed
public import Theory.SpecificGroups.SymmetricFive.TranspositionCentralizer
public import Theory.GroupTheory.Amalgam.DihedralTwelvePair.Models
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The exact escaping normalizer of an original seed involution

For the specified S5 marking of K/O2(K), let t be the proved seed involution
in the original Sylow subgroup and put A = O2(K)<t>. The relative normalizer
B = N_K(A) maps onto the transposition centralizer of order twelve. Its
intrinsic two-core is exactly A and B/A is S3. The original cubic normalizes
both A and B, and B itself escapes M.

This escape cannot replace the source invariant parabolic: neither A nor B
is normalized by the full original T, and BT = KT. The obstruction already
occurs in S5, where a Sylow two-group of order eight cannot lie in the
transposition centralizer of order twelve. The exact kernel calculation
transfers the obstruction from A to B. It does not contradict the source
6.1.19, which uses the different canonical Sylow overgroup in S5.

The final application retains the same original W/Z_S witness, seed,
covering kernels and marked quotient maps. The canonical S5 parabolic
escape and mixed-amalgam contradiction remain with
qt-d-1222-rankone-recognition-natural, as do initial 6.1.4–5, omega escape
and the remaining geometry through unconditional 6.1.27.
Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveSeedNormalizer
local notation "S5" => Equiv.Perm (Fin 5)
local notation "S3" => Equiv.Perm (Fin 3)

private theorem swap_normalizer (t : S5) (ht : t.IsSwap) :
    normalizer (zpowers t : Set S5) = centralizer ({t} : Set S5) := by
  have hc : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers,ht.orderOf]
  apply le_antisymm
  · intro g hg
    exact mem_centralizer_singleton_iff.mpr
      (normalizer_le_centralizer_of_card_two _ hc hg t (mem_zpowers t)).symm
  · intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    congr 1
    change g*t*g⁻¹=t
    rw [mem_centralizer_singleton_iff.mp hg,mul_inv_cancel_right]

private def dihedral_quotient :
    ((DihedralGroup 6) ⧸ pCore 2 (DihedralGroup 6)) ≃* S3 := by
  let e := RankTwoAmalgam.dihedralTwelveVertexEquiv.symm
  let f := (MonoidHom.snd RankTwoAmalgam.swapMiddle S3).comp e.toMonoidHom
  have hf : Function.Surjective f := by
    intro x
    exact ⟨e.symm (1,x),congrArg Prod.snd (e.apply_symm_apply (1,x))⟩
  have hk : IsPGroup 2 f.ker := by
    apply IsPGroup.of_card (n := 1)
    have hh := f.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top_of_surjective _ hf,card_top,
      DihedralGroup.nat_card,Nat.card_perm,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh ⊢
    omega
  exact (QuotientGroup.quotientMulEquivOfEq
    (ker_eq_twoCore_of_surjective_perm_three f hf hk).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)

private theorem preimage_normalizer {H : Type*} [Group H]
    (q : H →* S5) (hq : Function.Surjective q) (t : S5) (ht : t.IsSwap) :
    normalizer ((zpowers t).comap q : Set H) =
      (centralizer ({t} : Set S5)).comap q := by
  rw [←comap_normalizer_eq_of_surjective _ hq,swap_normalizer t ht]

private theorem preimage_normalizer_quotient {H : Type*} [Group H] [Finite H]
    (q : H →* S5) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (t : S5) (ht : t.IsSwap) :
    Nonempty ((normalizer ((zpowers t).comap q : Set H) ⧸
      pCore 2 (normalizer ((zpowers t).comap q : Set H))) ≃* S3) := by
  let C := centralizer ({t} : Set S5)
  let B := C.comap q
  have he : B.map q=C := map_comap_eq_self_of_surjective hq C
  let f : B →* C := (MulEquiv.subgroupCongr he).toMonoidHom.comp (q.subgroupMap B)
  have hf : Function.Surjective f := (MulEquiv.subgroupCongr he).surjective.comp
    (q.subgroupMap_surjective B)
  have hfk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr he).injective,
      ker_subgroupMap]
    exact hk.comap_subtype
  obtain ⟨e⟩ := Theory.SpecificGroups.SymmetricFive.transposition_centralizer_dihedral t ht
  rw [preimage_normalizer q hq t ht]
  exact ⟨(f.pCoreQuotientEquiv hf hfk).trans
    ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans dihedral_quotient)⟩

private theorem preimage_not_sylow_normalized {H : Type*} [Group H] [Finite H]
    (q : H →* S5) (hq : Function.Surjective q)
    (S : Sylow 2 H) (t : S5) (ht : t.IsSwap) :
    ¬ (S : Subgroup H) ≤ normalizer ((zpowers t).comap q : Set H) := by
  intro hn
  rw [preimage_normalizer q hq t ht] at hn
  have hm : ((S.mapSurjective hq : Sylow 2 S5) : Subgroup S5) ≤
      centralizer ({t} : Set S5) := map_le_iff_le_comap.mpr hn
  have hc : Nat.card (S.mapSurjective hq) = 8 := by
    rw [Sylow.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have hd := card_dvd_of_le hm
  have htC : Nat.card (centralizer ({t} : Set S5))=12 := by
    rw [Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp ht]
    norm_num
  rw [hc,htC] at hd
  norm_num at hd
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveSeedNormalizer

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

/-- The original transposition preimage has an S3 normalizer section.
Its normalizer cannot contain the whole original Sylow subgroup. -/
theorem natural_five_transposition_normalizer_section
    (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (t : K) (htT : (t : G) ∈ (T : Subgroup G))
    (ht : (e (QuotientGroup.mk' (pCore 2 K) t)).IsSwap) :
    let A := K.pCoreIn 2 ⊔ zpowers (t : G)
    let B := K ⊓ normalizer (A : Set G)
    Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
      (B.subgroupOf K).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) =
        centralizer ({e (QuotientGroup.mk' (pCore 2 K) t)} : Set (Equiv.Perm (Fin 5))) ∧
      B.pCoreIn 2 = A ∧ A.relIndex B = 6 ∧
      B ⊔ (T : Subgroup G) = K ⊔ (T : Subgroup G) ∧
      ¬ (T : Subgroup G) ≤ normalizer (A : Set G) ∧
      ¬ (T : Subgroup G) ≤ normalizer (B : Set G) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  change (q t).IsSwap at ht
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let A' := pCore 2 K ⊔ zpowers t
  let A := K.pCoreIn 2 ⊔ zpowers (t : G)
  let B := K ⊓ normalizer (A : Set G)
  have hAm : A'.map K.subtype = A := by rw [Subgroup.map_sup,MonoidHom.map_zpowers]; rfl
  have hAK : A ≤ K := sup_le (pCoreIn_le 2 K) (zpowers_le.mpr t.property)
  have hAs : A.subgroupOf K=A' := by
    rw [←hAm]
    exact comap_map_eq_self_of_injective K.subtype_injective A'
  have hAq : A'.map q = zpowers (q t) := by
    rw [show A'=q.ker ⊔ zpowers t from congrArg (fun H => H ⊔ zpowers t) hk.symm,
      Subgroup.map_sup,Subgroup.map_ker_self,MonoidHom.map_zpowers,bot_sup_eq]
  have hpre : (zpowers (q t)).comap q=A' := by
    rw [←hAq]
    exact comap_map_eq_self (hk ▸ (show pCore 2 K ≤ A' from le_sup_left))
  let B' := normalizer (A' : Set K)
  have hBm : B'.map K.subtype=B := by
    rw [show B'=normalizer (A' : Set K) from rfl,←hAs,←subgroupOf_normalizer_eq hAK,
      subgroupOf_map_subtype,inf_comm]
  let b := (B'.equivMapOfInjective K.subtype K.subtype_injective).trans (MulEquiv.subgroupCongr hBm)
  obtain ⟨eB⟩ := NaturalFiveSeedNormalizer.preimage_normalizer_quotient q hq (hk ▸ pCore_isPGroup) (q t) ht
  rw [hpre] at eB
  have hTQ : K.pCoreIn 2 ≤ (T : Subgroup G) := by
    obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
    have hh := pCoreIn_le_sylow K S
    rw [hS,subgroupOf_map_subtype] at hh
    exact hh.trans inf_le_left
  have hAT : A ≤ (T : Subgroup G) := sup_le hTQ (zpowers_le.mpr htT)
  let eBQ := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB
  have hAc : A ≤ B.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hAT)
      (le_inf hAK A.le_normalizer) inf_le_right
  have hBq : B'.map q = centralizer ({q t} : Set (Equiv.Perm (Fin 5))) := by
    rw [show B'=normalizer (A' : Set K) from rfl,←hpre,
      NaturalFiveSeedNormalizer.preimage_normalizer q hq (q t) ht]
    exact map_comap_eq_self_of_surjective hq _
  have hi : A.relIndex B = 6 := by
    rw [←hAm,←hBm,relIndex_map_map_of_injective _ _ K.subtype_injective]
    have hh := relIndex_map_map q A' B'
    have hkA : q.ker ≤ A' := hk ▸ (show pCore 2 K ≤ A' from le_sup_left)
    rw [sup_eq_left.mpr hkA,sup_eq_left.mpr (hkA.trans A'.le_normalizer),hAq,hBq] at hh
    have hAC : zpowers (q t) ≤ centralizer ({q t} : Set (Equiv.Perm (Fin 5))) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
    have hcard := relIndex_mul_relIndex (⊥ : Subgroup (Equiv.Perm (Fin 5)))
      (zpowers (q t)) (centralizer ({q t} : Set (Equiv.Perm (Fin 5)))) bot_le hAC
    have htwo : Nat.card (zpowers (q t))=2 := by rw [Nat.card_zpowers,ht.orderOf]
    have htwelve : Nat.card (centralizer ({q t} : Set (Equiv.Perm (Fin 5))))=12 := by
      rw [Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp ht]
      norm_num
    rw [relIndex_bot_left,relIndex_bot_left,htwo,htwelve,hh] at hcard
    change 2 * A'.relIndex B' = 12 at hcard
    omega
  have hci : (B.pCoreIn 2).relIndex B=6 := by
    change (((pCore 2 B).map B.subtype).comap B.subtype).index=6
    rw [comap_map_eq_self_of_injective B.subtype_injective,index_eq_card]
    exact (Nat.card_congr eBQ.toEquiv).trans (by
      rw [Nat.card_perm,Nat.card_fin]; rfl)
  have hcore : B.pCoreIn 2=A := by
    apply le_antisymm _ hAc
    apply relIndex_eq_one.mp
    have hh := relIndex_mul_relIndex A (B.pCoreIn 2) B hAc (pCoreIn_le 2 B)
    rw [hi,hci] at hh
    omega
  have hnot : ¬ (T : Subgroup G) ≤ normalizer (A : Set G) := by
    intro hn
    obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
    apply NaturalFiveSeedNormalizer.preimage_not_sylow_normalized q hq S (q t) ht
    rw [hpre,←hAs,←subgroupOf_normalizer_eq hAK,hS]
    exact fun x hx => hn hx
  have hgen : B ⊔ (T : Subgroup G) = K ⊔ (T : Subgroup G) := by
    obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
    have htS : t ∈ (S : Subgroup K) := by rw [hS]; exact htT
    have htop : ((S : Subgroup K) ⊔ B').map q = ⊤ := by
      rw [Subgroup.map_sup,hBq]
      exact Theory.SpecificGroups.SymmetricFive.TranspositionNormalizer.sylow_sup_centralizer_eq_top
        (S.mapSurjective hq) (q t) (mem_map_of_mem q htS) ht
    have hfull : (S : Subgroup K) ⊔ B'=⊤ := by
      have hh := congrArg (Subgroup.comap q) htop
      rwa [comap_map_eq_self (show q.ker ≤ (S : Subgroup K) ⊔ B' from
        (hk ▸ pCore_isPGroup.le_sylow_of_normal S).trans le_sup_left),comap_top] at hh
    have hKm : ((T : Subgroup G) ⊓ K) ⊔ B=K := by
      have hh := congrArg (Subgroup.map K.subtype) hfull
      rwa [Subgroup.map_sup,hBm,hS,subgroupOf_map_subtype,←MonoidHom.range_eq_map,range_subtype] at hh
    apply le_antisymm (sup_le_sup inf_le_left le_rfl)
    apply sup_le _ le_sup_right
    rw [←hKm]
    exact sup_le (inf_le_left.trans le_sup_right) le_sup_left
  have hBs : B.subgroupOf K=B' := by
    rw [←hBm]
    exact comap_map_eq_self_of_injective K.subtype_injective B'
  refine ⟨⟨eBQ⟩,by change (B.subgroupOf K).map q = _; rw [hBs]; exact hBq,
    hcore,hi,hgen,hnot,?_⟩
  intro hn
  apply hnot
  rw [←hcore]
  exact hn.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition


namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

/-- Escape occurs inside K itself, for the full transposition-preimage
normalizer, not merely somewhere in its ambient normalizer. -/
theorem natural_five_transposition_normalizer_escape
    (T : Sylow 2 G) (K M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) (hKM : ¬ K ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (t : K) (htT : (t : G) ∈ (T : Subgroup G))
    (ht : (e (QuotientGroup.mk' (pCore 2 K) t)).IsSwap) :
    ¬ K ⊓ normalizer ((K.pCoreIn 2 ⊔ zpowers (t : G) : Subgroup G) : Set G) ≤ M := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  have htS : t ∈ (S : Subgroup K) := by rw [hS]; exact htT
  have hSM : (S : Subgroup K) ≤ M.subgroupOf K := by
    rw [hS]
    exact fun x hx => hTM hx
  have hproper : M.subgroupOf K ≠ ⊤ := by
    intro he
    apply hKM
    intro x hx
    exact (show (⟨x,hx⟩ : K) ∈ M.subgroupOf K from he ▸ mem_top _)
  have hn := Theory.SpecificGroups.SymmetricFive.TranspositionNormalizer.quotient_normalizer_not_le_of_le_sylow
    q hq S (M.subgroupOf K) (zpowers t) hSM hproper
    (zpowers_le.mpr htS) (q t) ht (MonoidHom.map_zpowers q t)
  intro hBM
  apply hn
  intro x hx
  apply hBM
  refine ⟨x.property,?_⟩
  have hh := (q.ker ⊔ zpowers t).le_normalizer_map K.subtype
    (mem_map_of_mem K.subtype hx)
  rw [Subgroup.map_sup,hk,MonoidHom.map_zpowers] at hh
  change (x : G) ∈ normalizer ((K.pCoreIn 2 ⊔ zpowers (t : G) : Subgroup G) : Set G) at hh
  exact hh

/-- The actual escaping S3 normalizer has full two-core O2(N) joined
with the original involution. It is cubic-invariant and cannot be
T-invariant. This records the exact limitation of this local escape. -/
@[expose] def NaturalFiveSeedNormalizerData
    (T : Sylow 2 G) (L P N M : Subgroup G) : Prop :=
  let K := P ⊔ N.pCoreIn 2
  ∀ e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
    ∃ t : K, (t : G) ∈ (T : Subgroup G) ∧ (t : G) ∈ P ∧ orderOf t=2 ∧
      (e (QuotientGroup.mk' (pCore 2 K) t)).IsSwap ∧
      let A := N.pCoreIn 2 ⊔ zpowers (t : G)
      let B := K ⊓ normalizer (A : Set G)
      A ≤ (T : Subgroup G) ∧ ¬ B ≤ M ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
      (B.subgroupOf K).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) =
        centralizer ({e (QuotientGroup.mk' (pCore 2 K) t)} : Set (Equiv.Perm (Fin 5))) ∧
      B.pCoreIn 2=A ∧ A.relIndex B=6 ∧
      B ⊔ (T : Subgroup G) = K ⊔ (T : Subgroup G) ∧
      ¬ (T : Subgroup G) ≤ normalizer (A : Set G) ∧
      ¬ (T : Subgroup G) ≤ normalizer (B : Set G) ∧
      ∀ c : G, c ∈ L → c ∈ N → orderOf c=3 →
        c ∈ normalizer (A : Set G) ∧ c ∈ normalizer (B : Set G)

variable {T : Sylow 2 G} {L M R : Subgroup G}
/-- Apply the normalizer-section calculation to the same seed and cover,
preserving the entire original normalizer two-core. -/
theorem natural_five_seed_normalizer_data
    {X : Type*} [Group X]
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (σ : Escape.I (T : Subgroup G) L R →* MulAut X)
    (hPI : conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ≤
      Escape.I (T : Subgroup G) L R)
    (hc : NaturalInvariantCoverData T
      (conjugateSpanBy E (Escape.I (T : Subgroup G) L R))
      (Escape.I (T : Subgroup G) L R) (Escape.H (T : Subgroup G) L R) σ hPI)
    (hKM : ¬ (conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ⊔
      (Escape.H (T : Subgroup G) L R).pCoreIn 2) ≤ M) :
    NaturalFiveSeedNormalizerData T L
      (conjugateSpanBy E (Escape.I (T : Subgroup G) L R))
      (Escape.H (T : Subgroup G) L R) M := by
  have hd := natural_five_seed_escape_data h hnat E σ hPI hc hKM
  obtain ⟨hKI,hNK,hTK,hQ,_⟩ := hc
  intro e
  obtain ⟨_,t,htT,htP,ht2,ht,hAT,_,hcA⟩ := hd e
  have hsec := natural_five_transposition_normalizer_section T _ hTK e t htT ht
  have hout := natural_five_transposition_normalizer_escape T _ M h.sylow_le hTK hKM e t htT ht
  dsimp only at hsec hout
  rw [hQ] at hsec hout
  obtain ⟨he,hmap,hcore,hi,hgen,hnotA,hnotB⟩ := hsec
  refine ⟨t,htT,htP,ht2,ht,hAT,hout,he,hmap,hcore,hi,hgen,hnotA,hnotB,?_⟩
  intro c hcL hcN hc3
  have ha := hcA c hcL hcN hc3
  exact ⟨ha,inf_normalizer_le_normalizer_inf
    ⟨hNK hcN,(normalizer _).le_normalizer ha⟩⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- The same original W/Z_S witness retains its seed and maps, and has an
escaping cubic-invariant S3 normalizer with exact two-core and a proved
obstruction to full Sylow invariance. -/
theorem exists_ambient_amalgam_or_five_seed_normalizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N M ∧
            NaturalFiveCubicParabolicData T L R P N ∧
            NaturalThreeInvariantParabolicData T L R P N M ∧
            (NaturalEscapingAmalgamData T L R P N M ∨
              (NaturalFiveContainedParabolicData T P N M ∧
                NaturalFiveElementaryRestriction P N ∧
                NaturalFiveCubicFixedData T L R P N ∧
                NaturalFiveSpanActionData T L R (P ⊔ N.pCoreIn 2) ∧
                NaturalFiveFixedOrbitData T L R (P ⊔ N.pCoreIn 2) M ∧
                NaturalFiveSpanSeparationData T L R (P ⊔ N.pCoreIn 2) ∧
                NaturalFiveSpanRetractionData T L R (P ⊔ N.pCoreIn 2) ∧
                NaturalFiveSeedEscapeData T L E P N M ∧
                NaturalFiveSeedNormalizerData T L P N M ∧
                ∃ c t : G, c ∈ L ∧ c ∈ N ∧ orderOf c=3 ∧
                  t ∈ N.pCoreIn 2 ∧ orderOf t=2 ∧ c*t*c⁻¹=t ∧ t ∉ Z ∧ t ∉ conjugateSpanBy (layer L R) (P ⊔ N.pCoreIn 2) ∧
                  t ∈ centralizer (layer L R : Set G) ∧
                  t ∈ centralizer (conjugateSpanBy (layer L R)
                    ((P ⊔ N.pCoreIn 2) ⊓ centralizer (zpowers c : Set G)) : Set G))) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,ham⟩ :=
    d.exists_ambient_amalgam_or_five_seed_escape h hnat hE hs hNS hab
  let := hZ
  let := hX
  let := h.layer_elementary
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,?_⟩
  apply ham.imp_right
  rintro ⟨hd,hno,hfixed,hspan,horbit,hsep,hret,hseed,hobs⟩
  exact ⟨hd,hno,hfixed,hspan,horbit,hsep,hret,hseed,
    natural_five_seed_normalizer_data (hn ▸ h) (hn ▸ hnat) E σ hPI hcover hescape.2.1,hobs⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
