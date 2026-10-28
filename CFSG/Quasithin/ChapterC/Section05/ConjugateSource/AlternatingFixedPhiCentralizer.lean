module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFixedPhi
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveSylowFixed
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.Frattini.SquareImage

/-!
# Centralizing the fixed Frattini subgroup of paired alternating-five blocks

The exponent-two marked Baumann image kills Φ(I), placing it in the
opposite block's two-core U₂D₂. An element fixed by S∩L₂ has its U₂ factor
in the Sylow-fixed line. The normalizer of S∩L₂ fixes that line pointwise,
and L₂ centralizes D₂.

A proper Sylow overgroup of an A₅ block normalizes its Sylow subgroup:
pass to the actual A₅ quotient, then lift through the two-core. Thus the
Sylow subgroup of M∩L₂ is its characteristic two-core. The intersection
M∩(L₁L₂) normalizes it. Splitting each element along the two blocks proves
that this entire intersection centralizes the literal Φ, which in particular
proves the source's assertion for its prime-to-three residual.

Source: Aschbacher–Smith, proof of 2.4.25, printed p.541.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
namespace AlternatingFixedPhi
variable {G : Type*} [Group G] [Finite G]

private theorem proper_sylow_overgroup_normalizes_of_quotient
    {H D : Type*} [Group H] [Group D] [Finite H] [Finite D]
    (hcontrol : ∀ (Q : Sylow 2 D) (B : Subgroup D), B ≠ ⊤ →
      (Q : Subgroup D) ≤ B → B ≤ normalizer (Q : Set D))
    (q : H →* D) (hq : Function.Surjective q)
    (T : Sylow 2 H) (hkT : q.ker ≤ (T : Subgroup H))
    (A : Subgroup H) (hne : A ≠ ⊤) (hTA : (T : Subgroup H) ≤ A) :
    A ≤ normalizer (T : Set H) := by
  let T' := T.mapSurjective hq
  have hproper : A.map q ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.comap q) he
    rw [comap_map_eq_self (hkT.trans hTA),comap_top] at hh
    exact hne hh
  have hn := hcontrol T' (A.map q) hproper
    (map_mono hTA)
  change A.map q ≤ normalizer ((T : Subgroup H).map q : Set D) at hn
  intro a ha
  have hh := ((T : Subgroup H).map q).le_normalizer_comap q
    (hn (mem_map_of_mem q ha))
  rwa [comap_map_eq_self hkT] at hh

private theorem proper_sylow_overgroup_normalizes {H : Type*} [Group H] [Finite H]
    (hb : IsAlternatingBlock H 5) (T : Sylow 2 H)
    (A : Subgroup H) (hne : A ≠ ⊤) (hTA : (T : Subgroup H) ≤ A) :
    A ≤ normalizer (T : Set H) := by
  obtain ⟨r,⟨m⟩,hr⟩ := hb.2.2
  let q := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotientIso.injective,QuotientGroup.ker_mk']
  have hkT : q.ker ≤ (T : Subgroup H) := hk ▸ (pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal T
  exact proper_sylow_overgroup_normalizes_of_quotient
    alternatingGroup.proper_sylow_overgroup_le_normalizer q hq T hkT A hne hTA

variable {S K L : Subgroup G}

/-- The original Frattini subgroup lies in the two-core for the opposite marked block. -/
theorem P_le_opposite_core (h₂ : AlternatingPairSetup S L K) :
    P S K ≤ (L ⊔ ChapterB.baumann S).pCoreIn 2 := by
  let f : I S K →* FivePerm := h₂.action.comp
    (inclusion (show I S K ≤ L ⊔ ChapterB.baumann S from inf_le_left.trans le_sup_right))
  have hf (a : I S K) : f a ^ 2 = 1 := by
    have ha : f a ∈ ChapterB.Offenders.D 5 := by
      rw [←h₂.baumann_image]
      exact mem_map_of_mem h₂.action (show inclusion _ a ∈
        (ChapterB.baumann S).subgroupOf (L ⊔ ChapterB.baumann S) from a.property.1)
    let he := ChapterB.Offenders.Odd.isElementaryTwo_disjointTranspositions
      (n := 5) (m := 2) (Or.inl rfl) (by decide) (by decide)
    let : IsElementaryAbelian 2 (ChapterB.Offenders.D 5) := he.2
    exact elemPow_eq_one_of_isElementaryAbelian (f a) ha
  have hp := Theory.GroupTheory.frattini_le_ker_of_square_image f hf
  rintro g ⟨a,ha,rfl⟩
  rw [h₂.core]
  refine ⟨a.property.1,?_⟩
  have hh : h₂.action (inclusion (show I S K ≤ L ⊔ ChapterB.baumann S from
      inf_le_left.trans le_sup_right) a) = 1 := hp ha
  have hm : inclusion (show I S K ≤ L ⊔ ChapterB.baumann S from
      inf_le_left.trans le_sup_right) a ∈ h₂.action.ker := hh
  rw [h₂.action_kernel] at hm
  exact hm

private theorem proper_opposite_overgroup_normalizes_sylow
    (h₂ : AlternatingPairSetup S L K) (A : Subgroup G)
    (hAL : A ≤ L) (hA : A ≠ L) (hSA : S ⊓ L ≤ A) :
    A ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  let AL := A.subgroupOf L
  have hAT : AL ≠ ⊤ := by
    intro he
    apply hA
    have hh := congrArg (Subgroup.map L.subtype) he
    change (A.subgroupOf L).map L.subtype = (⊤ : Subgroup L).map L.subtype at hh
    simpa only [map_subgroupOf_eq_of_le hAL,←MonoidHom.range_eq_map,L.range_subtype] using hh
  have hTA : (h₂.sylow : Subgroup L) ≤ AL := by
    intro a ha
    exact hSA (h₂.sylow_image ▸ mem_map_of_mem L.subtype ha)
  have hn := proper_sylow_overgroup_normalizes h₂.block h₂.sylow AL hAT hTA
  apply le_normalizer_iff.mpr
  intro a ha u hu
  have hu' : (⟨u,hu.2⟩ : L) ∈ h₂.sylow := by
    have hh := hu
    rw [←h₂.sylow_image] at hh
    obtain ⟨v,hv,hvu⟩ := hh
    exact (Subtype.ext hvu : v = ⟨u,hu.2⟩) ▸ hv
  have hh := le_normalizer_iff.mp hn ⟨a,hAL ha⟩ ha ⟨u,hu.2⟩ hu'
  rw [←h₂.sylow_image]
  exact mem_map_of_mem L.subtype hh

private theorem normalizer_centralizes_sylow_fixed
    (h₂ : AlternatingPairSetup S L K) (A : Subgroup G)
    (hAL : A ≤ L) (hAN : A ≤ normalizer ((S ⊓ L : Subgroup G) : Set G)) :
    A ≤ centralizer (sourceModule L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) : Set G) := by
  let AL := A.subgroupOf L
  have hn : AL ≤ normalizer (h₂.sylow : Set L) := by
    apply le_normalizer_iff.mpr
    intro a ha u hu
    have huS : (u : G) ∈ S ⊓ L := by
      rw [←h₂.sylow_image]
      exact mem_map_of_mem L.subtype hu
    have hh := le_normalizer_iff.mp hAN (a : G) ha (u : G) huS
    rw [←h₂.sylow_image] at hh
    obtain ⟨v,hv,hvconj⟩ := hh
    exact (Subtype.ext hvconj : v = a*u*a⁻¹) ▸ hv
  let E := blockU L ⊓ centralizer (h₂.sylow : Set L)
  have hnE : AL ≤ normalizer (E : Set L) :=
    (le_inf (le_top.trans ((blockU L).normalizer_eq_top.symm.le))
      (hn.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  have hc : AL ≤ centralizer (E : Set L) := by
    by_cases he : E = ⊥
    · rw [he]
      intro a ha b hb
      have hb1 : b = 1 := hb
      simp only [hb1,mul_one,one_mul]
    · have hsmall := h₂.block.sylow_fixed_card_le_two h₂.sylow
      change Nat.card E ≤ 2 at hsmall
      have hpos := E.one_lt_card_iff_ne_bot.mpr he
      exact hnE.trans (normalizer_le_centralizer_of_card_two E (by omega))
  intro a ha u hu
  obtain ⟨uL,huL,rfl⟩ := hu.1
  have huE : uL ∈ E := by
    refine ⟨huL,?_⟩
    intro t ht
    have htS : (t : G) ∈ S ⊓ L := by
      rw [←h₂.sylow_image]
      exact mem_map_of_mem L.subtype ht
    exact Subtype.ext (hu.2 t htS)
  exact congrArg Subtype.val (hc (show (⟨a,hAL ha⟩ : L) ∈ AL from ha) uL huE)

/-- The opposite block's Sylow normalizer centralizes the literal fixed Φ. -/
theorem opposite_sylow_normalizer_centralizes_Phi
    (h₁ : AlternatingPairSetup S K L) (h₂ : AlternatingPairSetup S L K)
    (A : Subgroup G) (hAL : A ≤ L) (hAN : A ≤ normalizer ((S ⊓ L : Subgroup G) : Set G)) :
    A ≤ centralizer (Phi S K : Set G) := by
  have hfix := normalizer_centralizes_sylow_fixed h₂ A hAL hAN
  have hsplit : P S K ≤ sourceModule L ⊔ (ChapterB.baumann S ⊓ centralizer (L : Set G)) :=
    (P_le_opposite_core h₂).trans_eq h₂.product
  have hc : ChapterB.baumann S ⊓ centralizer (L : Set G) ≤ centralizer (sourceModule L : Set G) :=
    inf_le_right.trans (centralizer_le (map_subtype_le _))
  intro a ha v hv
  have hv' : v ∈ (sourceModule L : Set G) *
      (ChapterB.baumann S ⊓ centralizer (L : Set G) : Set G) := by
    have he := coe_mul_of_right_le_normalizer_left (sourceModule L)
      (ChapterB.baumann S ⊓ centralizer (L : Set G)) (hc.trans (Subgroup.centralizer_le_normalizer _))
    change v ∈ (sourceModule L : Set G) * ((ChapterB.baumann S ⊓ centralizer (L : Set G) : Subgroup G) : Set G)
    rw [←he]
    exact hsplit hv.1
  obtain ⟨u,hu,d,hd,rfl⟩ := hv'
  have huS : u ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro s hs
    have hsI : s ∈ SI S K := ⟨hs.1,Subgroup.centralizer_le_normalizer _ (h₁.commute hs.2)⟩
    have hh := hv.2 s hsI
    have hdS := hd.2 s hs.2
    apply mul_right_cancel (b := d)
    calc
      s * u * d = s * (u * d) := mul_assoc _ _ _
      _ = (u * d) * s := hh
      _ = u * (d * s) := mul_assoc _ _ _
      _ = u * (s * d) := congrArg (u * ·) hdS.symm
      _ = u * s * d := (mul_assoc _ _ _).symm
  have hua := hfix ha u ⟨hu,huS⟩
  have hda := hd.2 a (hAL ha)
  calc
    (u*d)*a = u*(d*a) := mul_assoc _ _ _
    _ = u*(a*d) := by rw [←hda]
    _ = a*(u*d) := by rw [←mul_assoc,hua,mul_assoc]

/-- Every proper opposite-block Sylow overgroup centralizes the literal fixed Φ. -/
theorem proper_opposite_overgroup_centralizes_Phi
    (h₁ : AlternatingPairSetup S K L) (h₂ : AlternatingPairSetup S L K)
    (A : Subgroup G) (hAL : A ≤ L) (hA : A ≠ L) (hSA : S ⊓ L ≤ A) :
    A ≤ centralizer (Phi S K : Set G) :=
  opposite_sylow_normalizer_centralizes_Phi h₁ h₂ A hAL
    (proper_opposite_overgroup_normalizes_sylow h₂ A hAL hA hSA)

private theorem intersection_core_eq_sylow
    (h₂ : AlternatingPairSetup S L K) (M : Subgroup G)
    (hSL : S ⊓ L ≤ M) (hLM : ¬ L ≤ M) :
    (M ⊓ L).pCoreIn 2 = S ⊓ L := by
  have hproper : M ⊓ L ≠ L := fun he => hLM (he.ge.trans inf_le_left)
  have hRB : S ⊓ L ≤ M ⊓ L := le_inf hSL inf_le_right
  have hn := proper_opposite_overgroup_normalizes_sylow h₂ (M ⊓ L) inf_le_right hproper hRB
  have hRQ := le_pCoreIn_of_normalizes (h₂.twoGroup.to_le (show S ⊓ L ≤ S from inf_le_left)) hRB hn
  have hQL : (M ⊓ L).pCoreIn 2 ≤ L := (pCoreIn_le 2 (M ⊓ L)).trans inf_le_right
  have hp : IsPGroup 2 (((M ⊓ L).pCoreIn 2).subgroupOf L) :=
    (isPGroup_pCoreIn 2 (M ⊓ L)).comap_subtype
  have hle : (h₂.sylow : Subgroup L) ≤ ((M ⊓ L).pCoreIn 2).subgroupOf L := by
    intro u hu
    apply hRQ
    rw [←h₂.sylow_image]
    exact mem_map_of_mem L.subtype hu
  have he := h₂.sylow.is_maximal' hp hle
  have hm := congrArg (Subgroup.map L.subtype) he
  rwa [map_subgroupOf_eq_of_le hQL,h₂.sylow_image] at hm

/-- The whole source intersection with the two-block product centralizes Φ.
The original properness and Sylow containment replace a Borel product premise. -/
theorem intersection_centralizes_Phi
    (h₁ : AlternatingPairSetup S K L) (h₂ : AlternatingPairSetup S L K)
    (M : Subgroup G) (hSL : S ⊓ L ≤ M) (hLM : ¬ L ≤ M) :
    M ⊓ (K ⊔ L) ≤ centralizer (Phi S K : Set G) := by
  let J := M ⊓ (K ⊔ L)
  have hKN : K ≤ centralizer (L : Set G) := le_centralizer_iff.mp h₁.commute
  have hJN : J ≤ normalizer (L : Set G) :=
    inf_le_right.trans (sup_le (hKN.trans (Subgroup.centralizer_le_normalizer _)) L.le_normalizer)
  have hJB : J ≤ normalizer ((M ⊓ L : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans M.le_normalizer) hJN).trans inf_normalizer_le_normalizer_inf
  have hJR : J ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [←intersection_core_eq_sylow h₂ M hSL hLM]
    exact hJB.trans (normalizer_le_normalizer_characteristic_image (M ⊓ L) (pCore 2 (M ⊓ L : Subgroup G)))
  have hKC : K ≤ centralizer (Phi S K : Set G) := le_centralizer_iff.mp (Phi_le_centralizer S K)
  have hLC := opposite_sylow_normalizer_centralizes_Phi h₁ h₂
    (L ⊓ normalizer ((S ⊓ L : Subgroup G) : Set G)) inf_le_left inf_le_right
  rintro y ⟨hyM,hyKL⟩
  have hy' : y ∈ (K : Set G) * (L : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left K L
      (h₁.commute.trans (Subgroup.centralizer_le_normalizer _))]
    exact hyKL
  obtain ⟨k,hk,l,hl,rfl⟩ := hy'
  have hkR : k ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ ((centralizer_le (show S ⊓ L ≤ L from inf_le_right)) (hKN hk))
  have hlR : l ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    have hh := (normalizer ((S ⊓ L : Subgroup G) : Set G)).mul_mem
      ((normalizer ((S ⊓ L : Subgroup G) : Set G)).inv_mem hkR) (hJR ⟨hyM,mul_mem_sup hk hl⟩)
    simpa only [inv_mul_cancel_left] using hh
  exact (centralizer (Phi S K : Set G)).mul_mem (hKC hk) (hLC ⟨hl,hlR⟩)

end AlternatingFixedPhi
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
