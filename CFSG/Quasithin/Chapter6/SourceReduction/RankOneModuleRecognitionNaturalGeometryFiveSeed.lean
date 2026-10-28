module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveRetraction
public import Theory.SpecificGroups.SymmetricFive.TranspositionNormalizer
public import Theory.SpecificGroups.SymmetricFiveInvolutions

/-!
# Actual seed involutions and escaping full-preimage normalizers

The even preimage of any specified S5 two-core marking is preserved by
N_G(K). If the original elementary seed lay in that preimage, so would
its I-conjugate span and O2(K), contradicting their generation of K.
Thus the original seed contains an actual involution whose marked image
is a transposition. Sylow conjugacy inside K places such an involution
in the original T while keeping it in the original conjugate span P.

The full preimage of its transposition subgroup is O2(K) joined with the
involution. Its normalizer escapes every proper overgroup containing the
original Sylow intersection. Each original cubic normalizes this actual
preimage because its action on the specified S5 quotient is trivial.
The literal Chapter12 application keeps the same W/Z_S witness and maps.

This supplies an ambient involution and normalizer escape. It does not
assert full T-invariance of that subgroup or lift an elementary even plane.
The canonical S5 parabolic escape, mixed-amalgam contradiction, initial
6.1.4–5, omega escape and remaining geometry through unconditional 6.1.27
stay with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveSeed
local notation "S5" => Equiv.Perm (Fin 5)

private theorem quotient_even_normalized {G : Type*} [Group G]
    (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* S5) :
    normalizer (K : Set G) ≤ normalizer
      (((alternatingGroup (Fin 5)).comap
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map K.subtype : Set G) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let A := (alternatingGroup (Fin 5)).comap q
  intro g hg
  have hforward (g : G) (hg : g ∈ normalizer (K : Set G)) :
      ∀ x ∈ A.map K.subtype, g*x*g⁻¹ ∈ A.map K.subtype := by
    rintro _ ⟨x,hx,rfl⟩
    let a := K.normalizerMonoidHom ⟨g,hg⟩
    let b := (MulAut.congr e) ((pCore 2 K).quotientAut a)
    obtain ⟨s,hs⟩ := Equiv.Perm.conj_surjective_of_degree (by decide : 5 ≤ 5) (by decide) b
    have he : q (a x)=b (q x) := by
      simp only [q,b,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.congr_apply,
        MulEquiv.trans_apply,e.symm_apply_apply,quotientAut_apply_mk]
    refine ⟨a x,?_,rfl⟩
    change q (a x) ∈ alternatingGroup (Fin 5)
    rw [he,←hs]
    exact (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem (q x) hx s
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hforward g hg x
  · intro hx
    have hh := hforward g⁻¹ ((normalizer (K : Set G)).inv_mem hg) (g*x*g⁻¹) hx
    convert hh using 1
    group

private theorem seed_transposition {G : Type*} [Group G]
    (E I K : Subgroup G) [IsElementaryAbelian 2 E]
    (hEK : E ≤ K) (hIK : I ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* S5)
    (hgen : conjugateSpanBy E I ⊔ K.pCoreIn 2 = K) :
    ∃ t : K, (t : G) ∈ E ∧ orderOf t=2 ∧
      (e (QuotientGroup.mk' (pCore 2 K) t)).IsSwap := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let A := (alternatingGroup (Fin 5)).comap q
  have hex : ∃ t : K, (t : G) ∈ E ∧ q t ∉ alternatingGroup (Fin 5) := by
    by_contra hn
    have hEA : E ≤ A.map K.subtype := by
      intro t ht
      refine ⟨⟨t,hEK ht⟩,?_,rfl⟩
      exact Classical.byContradiction (fun hnot => hn ⟨⟨t,hEK ht⟩,ht,hnot⟩)
    have hPA : conjugateSpanBy E I ≤ A.map K.subtype := by
      apply (closure_le _).mpr
      rintro _ ⟨g,hg,t,ht,rfl⟩
      exact (mem_normalizer_iff.mp ((hIK.trans (quotient_even_normalized K e)) hg) t).mp (hEA ht)
    have hQA : K.pCoreIn 2 ≤ A.map K.subtype := by
      rintro _ ⟨x,hx,rfl⟩
      refine ⟨x,?_,rfl⟩
      change e (QuotientGroup.mk' (pCore 2 K) x) ∈ alternatingGroup (Fin 5)
      rw [show QuotientGroup.mk' (pCore 2 K) x=1 from (QuotientGroup.eq_one_iff x).mpr hx,map_one]
      exact one_mem _
    have hKA : K ≤ A.map K.subtype := hgen.symm.le.trans (sup_le hPA hQA)
    have hall : ∀ y : S5, y ∈ alternatingGroup (Fin 5) := by
      intro y
      obtain ⟨t,ht⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) y
      obtain ⟨x,hx,hxt⟩ := hKA t.property
      have he : x=t := Subtype.ext hxt
      exact ht ▸ (he ▸ hx)
    have hh := hall (Equiv.swap 0 1)
    have he : (-1 : ℤˣ) = 1 := by
      simpa only [Equiv.Perm.mem_alternatingGroup,Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 1)] using hh
    exact (by decide : (-1 : ℤˣ) ≠ 1) he
  obtain ⟨t,ht,ho⟩ := hex
  have ht2 : t^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian _ ht)
  have hqne : q t ≠ 1 := fun he => ho (he ▸ one_mem _)
  have hqt2 : orderOf (q t)=2 := orderOf_eq_prime (by rw [←map_pow,ht2,map_one]) hqne
  exact ⟨t,ht,orderOf_eq_prime ht2 (fun he => hqne (by rw [he,map_one])),
    Equiv.Perm.five_isSwap_of_outer_involution (q t) hqt2 ho⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveSeed

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

omit [Finite G] in
/-- The original elementary seed has an actual involution with transposition
image under every specified S5 marking of its full invariant cover. -/
theorem natural_five_seed_involution
    (E K : Subgroup G) [IsElementaryAbelian 2 E]
    (hEK : E ≤ K)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hgen : conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ⊔ K.pCoreIn 2 = K) :
    ∃ t : K, (t : G) ∈ E ∧ orderOf t=2 ∧
      (e (QuotientGroup.mk' (pCore 2 K) t)).IsSwap :=
  NaturalFiveSeed.seed_transposition E _ K hEK
    ((Subgroup.centralizer_le_normalizer _).trans hNK) e hgen

/-- The same seed yields an involution in the original Sylow intersection.
The normalizer of its full two-core preimage escapes M. Every original
cubic normalizes that actual preimage. Full Sylow invariance is not asserted. -/
theorem natural_five_seed_normalizer_escape
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (E K : Subgroup G) [IsElementaryAbelian 2 E]
    (hEK : E ≤ K) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    (hgen : conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ⊔ K.pCoreIn 2 = K) :
    ∃ t : K, (t : G) ∈ (T : Subgroup G) ∧
      (t : G) ∈ conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ∧
      orderOf t=2 ∧ (e (QuotientGroup.mk' (pCore 2 K) t)).IsSwap ∧
      let A := K.pCoreIn 2 ⊔ zpowers (t : G)
      A ≤ (T : Subgroup G) ∧ ¬ normalizer (A : Set G) ≤ M ∧
      ∀ c : G, c ∈ L → c ∈ Escape.H (T : Subgroup G) L R → orderOf c=3 →
        c ∈ normalizer (A : Set G) := by
  let I := Escape.I (T : Subgroup G) L R
  let P := conjugateSpanBy E I
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hTK := h.sylow_normalizes_ZS.trans hNK
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  obtain ⟨x,hx,hx2,hxswap⟩ := natural_five_seed_involution E K hEK hNK e hgen
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hx2,pow_one])
  obtain ⟨S₀,hS₀⟩ := hp.exists_le_sylow
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq K S₀ S
  let t := (MulAut.conj k) x
  have htS : t ∈ (S : Subgroup K) := by
    rw [←hk]
    exact mem_map_of_mem (MulAut.conj k).toMonoidHom (hS₀ (mem_zpowers x))
  have htT : (t : G) ∈ (T : Subgroup G) := by rw [hS] at htS; exact htS
  have htP : (t : G) ∈ P :=
    (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy E I (hKI k.property)) x).mp
      (le_conjugateSpanBy E I hx)
  have ht2 : orderOf t=2 := ((MulAut.conj k).orderOf_eq x).trans hx2
  have htswap : (q t).IsSwap := by
    obtain ⟨i,j,hij,hijq⟩ := hxswap
    change (q (k*x*k⁻¹)).IsSwap
    rw [map_mul,map_mul,map_inv,show q x=Equiv.swap i j from hijq,
      Equiv.mul_swap_eq_swap_mul,mul_inv_cancel_right]
    exact Equiv.Perm.swap_isSwap_iff.mpr ((q k).injective.ne hij)
  have hQT : K.pCoreIn 2 ≤ T := by
    have hh := pCoreIn_le_sylow K S
    rw [hS,subgroupOf_map_subtype] at hh
    exact hh.trans inf_le_left
  let A := K.pCoreIn 2 ⊔ zpowers (t : G)
  have hAK : A ≤ K := sup_le (pCoreIn_le 2 K) (zpowers_le.mpr t.property)
  refine ⟨t,htT,htP,ht2,htswap,sup_le hQT (zpowers_le.mpr htT),?_,?_⟩
  · have hproper : M.subgroupOf K ≠ ⊤ := by
      intro he
      apply hKM
      intro y hy
      exact (show (⟨y,hy⟩ : K) ∈ M.subgroupOf K from he ▸ mem_top _)
    have hSP : (S : Subgroup K) ≤ M.subgroupOf K := by
      rw [hS]
      exact fun y hy => h.sylow_le hy
    have hn := Theory.SpecificGroups.SymmetricFive.TranspositionNormalizer.quotient_normalizer_not_le_of_le_sylow
      q hq S (M.subgroupOf K) (zpowers t) hSP hproper
      (zpowers_le.mpr htS) (q t) htswap (MonoidHom.map_zpowers q t)
    intro hNM
    apply hn
    intro y hy
    have hm := (q.ker ⊔ zpowers t).le_normalizer_map K.subtype (mem_map_of_mem K.subtype hy)
    have he : (q.ker ⊔ zpowers t).map K.subtype = A := by
      rw [Subgroup.map_sup,hqk,MonoidHom.map_zpowers]
      rfl
    rw [he] at hm
    exact hNM hm
  · intro c hcL hcN hc3
    exact le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono hAK le_rfl).trans
        (natural_five_cubic_quotient_trivial h hnat K hKI hNK e hcL hcN hc3)).trans
          (show K.pCoreIn 2 ≤ A from le_sup_left)) (mem_zpowers c)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- An original elementary seed and a Sylow-positioned involution, with their
specified transposition images and the escaping normalizer of the full
covering preimage. This does not assert a T-invariant S3 parabolic. -/
@[expose] def NaturalFiveSeedEscapeData
    (T : Sylow 2 G) (L E P N M : Subgroup G) : Prop :=
  let K := P ⊔ N.pCoreIn 2
  ∀ e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
    (∃ x : K, (x : G) ∈ E ∧ orderOf x=2 ∧
      (e (QuotientGroup.mk' (pCore 2 K) x)).IsSwap) ∧
    ∃ t : K, (t : G) ∈ (T : Subgroup G) ∧ (t : G) ∈ P ∧
      orderOf t=2 ∧ (e (QuotientGroup.mk' (pCore 2 K) t)).IsSwap ∧
      let A := N.pCoreIn 2 ⊔ zpowers (t : G)
      A ≤ (T : Subgroup G) ∧ ¬ normalizer (A : Set G) ≤ M ∧
      ∀ c : G, c ∈ L → c ∈ N → orderOf c=3 → c ∈ normalizer (A : Set G)

/-- Apply seed generation in the original invariant cover; its two-core
is the original normalizer two-core throughout the escape assertion. -/
theorem natural_five_seed_escape_data
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
    NaturalFiveSeedEscapeData T L E
      (conjugateSpanBy E (Escape.I (T : Subgroup G) L R))
      (Escape.H (T : Subgroup G) L R) M := by
  obtain ⟨hKI,hNK,_,hQ,_⟩ := hc
  intro e
  have hEK := (le_conjugateSpanBy E (Escape.I (T : Subgroup G) L R)).trans
    (show conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ≤
      conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ⊔
        (Escape.H (T : Subgroup G) L R).pCoreIn 2 from le_sup_left)
  have hgen : conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ⊔
      (conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ⊔
        (Escape.H (T : Subgroup G) L R).pCoreIn 2).pCoreIn 2 =
      conjugateSpanBy E (Escape.I (T : Subgroup G) L R) ⊔
        (Escape.H (T : Subgroup G) L R).pCoreIn 2 := by rw [hQ]
  refine ⟨natural_five_seed_involution E _ hEK hNK e hgen,?_⟩
  have hh := natural_five_seed_normalizer_escape h hnat E _ hEK hKI hNK hKM e hgen
  simpa only [hQ] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- The same original W/Z_S witness has a seed involution with transposition
image and an escaping normalizer of its full two-core preimage in the Sylow. -/
theorem exists_ambient_amalgam_or_five_seed_escape
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
                ∃ c t : G, c ∈ L ∧ c ∈ N ∧ orderOf c=3 ∧
                  t ∈ N.pCoreIn 2 ∧ orderOf t=2 ∧ c*t*c⁻¹=t ∧ t ∉ Z ∧ t ∉ conjugateSpanBy (layer L R) (P ⊔ N.pCoreIn 2) ∧
                  t ∈ centralizer (layer L R : Set G) ∧
                  t ∈ centralizer (conjugateSpanBy (layer L R)
                    ((P ⊔ N.pCoreIn 2) ⊓ centralizer (zpowers c : Set G)) : Set G))) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,ham⟩ :=
    d.exists_ambient_amalgam_or_five_retracted_core h hnat hE hs hNS hab
  let := hZ
  let := hX
  let := h.layer_elementary
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,?_⟩
  apply ham.imp_right
  rintro ⟨hd,hno,hfixed,hspan,horbit,hsep,hret,hobs⟩
  exact ⟨hd,hno,hfixed,hspan,horbit,hsep,hret,
    natural_five_seed_escape_data (hn ▸ h) (hn ▸ hnat) E σ hPI hcover hescape.2.1,hobs⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
