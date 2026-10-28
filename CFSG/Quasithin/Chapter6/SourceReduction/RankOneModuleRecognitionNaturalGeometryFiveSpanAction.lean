module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveFixedLayer

/-!
# Faithful S5 action on the original natural-layer span

Coprime fixed-point lifting covers the specified K/O2(K) marking by C_K(c).
The two-core of K lies in the original Sylow and normalizes the natural
layer. Thus C_K(c) and K generate exactly the same layer span. The proved
fixed-core centralization now holds on this entire ambient subgroup.

Conjugation by C_K(c) descends to S5 on that span. This action is faithful:
a nontrivial kernel would give a two-group quotient of S5. The original
Sylow already stabilizes the layer and covers that quotient, forcing K
to normalize the layer and hence lie in M, contrary to its proved escape.
In the abelian branch the span is elementary, its S5 action fixes Z_S,
and it commutes with the original cubic's conjugation automorphism.

The final theorem retains the same W/Z_S witness and both quotient maps.
An action on the ambient span is not an elementary subgroup lifting from
S5. S5 parabolic escape, the mixed-amalgam contradiction, initial 6.1.4–5,
omega escape and unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.

Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`),
using the original cubic and the faithful marked natural layer.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

private theorem five_core_le_sylow (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) : K.pCoreIn 2 ≤ T := by
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  have hh := pCoreIn_le_sylow K S
  rw [hS,subgroupOf_map_subtype] at hh
  exact hh.trans inf_le_left

omit [Finite G] in
private theorem five_fixed_representative (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5)) (c : G)
    (hf : Function.Surjective ((e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).comp
      (inclusion (show K ⊓ centralizer (zpowers c : Set G) ≤ K from inf_le_left))))
    (k : K) : ∃ d : (K ⊓ centralizer (zpowers c : Set G) : Subgroup G),
      e (QuotientGroup.mk' (pCore 2 K) (inclusion inf_le_left d)) =
        e (QuotientGroup.mk' (pCore 2 K) k) ∧
      (d : G)⁻¹ * (k : G) ∈ K.pCoreIn 2 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  obtain ⟨d,hd⟩ := hf (q k)
  refine ⟨d,hd,?_⟩
  have hk : (inclusion (show K ⊓ centralizer (zpowers c : Set G) ≤ K from inf_le_left) d)⁻¹ * k ∈
      pCore 2 K := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply e.injective
    change q (_⁻¹*k)=e 1
    rw [map_one,map_mul,map_inv]
    change (q (inclusion inf_le_left d))⁻¹ * q k=1
    rw [show q (inclusion inf_le_left d)=q k from hd,inv_mul_cancel]
  exact mem_map_of_mem K.subtype hk

/-- The cubic-fixed representatives generate exactly the full cover's
conjugate span of the original natural layer. -/
theorem natural_five_fixed_span_eq
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    conjugateSpanBy (layer L R) (K ⊓ centralizer (zpowers c : Set G)) =
      conjugateSpanBy (layer L R) K := by
  have hf := natural_five_cubic_fixed_cover h hnat K hKI hNK e hcL hcN hc3
  have hQV := (five_core_le_sylow K (h.sylow_normalizes_ZS.trans hNK)).trans
    h.sylow_normalizes_layer
  apply le_antisymm (conjugateSpanBy_mono le_rfl inf_le_left)
  rw [conjugateSpanBy_eq_iSup_conj]
  apply iSup_le
  intro k
  obtain ⟨d,_,hd⟩ := five_fixed_representative K e c hf k
  rintro _ ⟨x,hx,rfl⟩
  have hxq := (mem_normalizer_iff.mp (hQV hd) x).mp hx
  have hh := (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy (layer L R)
    (K ⊓ centralizer (zpowers c : Set G)) d.property) _).mp (le_conjugateSpanBy _ _ hxq)
  convert hh using 1
  dsimp
  group

/-- The full fixed two-core centralizes all K-conjugates of the natural
layer, not only the conjugates by C_K(c). -/
theorem natural_five_fixed_core_centralizes_span
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    (Escape.H (T : Subgroup G) L R).pCoreIn 2 ⊓ centralizer (zpowers c : Set G) ≤
      centralizer (conjugateSpanBy (layer L R) K : Set G) := by
  rw [←natural_five_fixed_span_eq h hnat K hKI hNK e hcL hcN hc3]
  exact natural_four_fixed_core_centralizes_fixed_span h hnat K
    (hKI.trans (Subgroup.centralizer_le_normalizer _)) hcL hc3

omit [Finite G] in
private theorem five_core_le_normalizer_core (K N : Subgroup G)
    (hKN : K ≤ N) (hNK : N ≤ normalizer (K : Set G)) : K.pCoreIn 2 ≤ N.pCoreIn 2 := by
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K)
    ((pCoreIn_le 2 K).trans hKN)
    (hNK.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))

/-- Descend conjugation by the cubic centralizer through the specified S5
marking to an action on the literal ambient natural-layer span. -/
theorem natural_five_span_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    ∃ τ : Equiv.Perm (Fin 5) →* MulAut (conjugateSpanBy (layer L R) K),
      ∀ d : (K ⊓ centralizer (zpowers c : Set G) : Subgroup G), ∀ x : conjugateSpanBy (layer L R) K,
        (τ (e (QuotientGroup.mk' (pCore 2 K) (inclusion inf_le_left d))) x : G) =
          (d : G) * x * (d : G)⁻¹ := by
  let C := K ⊓ centralizer (zpowers c : Set G)
  let S := conjugateSpanBy (layer L R) K
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f := q.comp (inclusion (show C ≤ K from inf_le_left))
  have hf : Function.Surjective f := natural_five_cubic_fixed_cover h hnat K hKI hNK e hcL hcN hc3
  have hCS : C ≤ normalizer (S : Set G) := inf_le_left.trans (le_normalizer_conjugateSpanBy _ _)
  let a : C →* MulAut S := S.normalizerMonoidHom.comp (inclusion hCS)
  have hker : f.ker ≤ a.ker := by
    intro d hd
    have hdQ : (inclusion (show C ≤ K from inf_le_left) d) ∈ pCore 2 K := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.injective (hd.trans e.map_one.symm)
    have hdN : (d : G) ∈ (Escape.H (T : Subgroup G) L R).pCoreIn 2 :=
      five_core_le_normalizer_core K _ (hKI.trans (Subgroup.centralizer_le_normalizer _))
        hNK (mem_map_of_mem K.subtype hdQ)
    have hdS := natural_five_fixed_core_centralizes_span h hnat K hKI hNK e hcL hcN hc3
      ⟨hdN,d.property.2⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (d : G)*(x : G)*(d : G)⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr (hdS x x.property).symm
  let b := QuotientGroup.liftEquiv f.ker hf rfl
  let τ := (QuotientGroup.lift f.ker a hker).comp b.symm.toMonoidHom
  refine ⟨τ,?_⟩
  intro d x
  have hb : b.symm (f d) = QuotientGroup.mk' f.ker d := by
    apply b.injective
    rw [b.apply_symm_apply]
    exact (QuotientGroup.liftEquiv_coe f.ker hf rfl d).symm
  have he : τ (f d) = a d := by
    change QuotientGroup.lift f.ker a hker (b.symm (f d))=a d
    rw [hb]
    rfl
  change (τ (f d) x : G)=_
  rw [he]
  rfl

private theorem sylow_and_kernel_generate {A B : Type*} [Group A] [Group B] [Finite A]
    (P : Sylow 2 A) (f : A →* B) (hf : Function.Surjective f) (hB : IsPGroup 2 B)
    (J : Subgroup A) (hPJ : (P : Subgroup A) ≤ J) (hkJ : f.ker ≤ J) : J=⊤ := by
  have htop : (P.mapSurjective hf : Subgroup B)=⊤ :=
    ((P.mapSurjective hf).is_maximal' (hB.to_subgroup ⊤) le_top).symm
  apply top_unique
  intro x _
  have hx : f x ∈ (P : Subgroup A).map f := by
    change f x ∈ (P.mapSurjective hf : Subgroup B)
    rw [htop]
    trivial
  obtain ⟨s,hs,he⟩ := hx
  have hxs : x*s⁻¹ ∈ f.ker := by
    change f (x*s⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  simpa only [inv_mul_cancel_right] using J.mul_mem (hkJ hxs) (hPJ hs)

/-- Escape from M forces the S5 action on the actual layer span to be
faithful. The kernel of a nonfaithful action would give a two-group
quotient, already covered by the original Sylow's layer stabilizer. -/
theorem natural_five_span_action_faithful
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    ∃ τ : Equiv.Perm (Fin 5) →* MulAut (conjugateSpanBy (layer L R) K),
      Function.Injective τ ∧
      ∀ d : (K ⊓ centralizer (zpowers c : Set G) : Subgroup G), ∀ x : conjugateSpanBy (layer L R) K,
        (τ (e (QuotientGroup.mk' (pCore 2 K) (inclusion inf_le_left d))) x : G) =
          (d : G) * x * (d : G)⁻¹ := by
  obtain ⟨τ,hτ⟩ := natural_five_span_action h hnat K hKI hNK e hcL hcN hc3
  refine ⟨τ,?_,hτ⟩
  by_contra hn
  have hk : τ.ker ≠ ⊥ := fun he => hn ((MonoidHom.ker_eq_bot_iff τ).mp he)
  have hp := symmetric_normal_quotient_two (by decide : 5 ≤ 5) τ.ker hk
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f := (QuotientGroup.mk' τ.ker).comp q
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective τ.ker).comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hTK := h.sylow_normalizes_ZS.trans hNK
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  let J := (normalizer (layer L R : Set G)).subgroupOf K
  have hPJ : (P : Subgroup K) ≤ J := by
    rw [hP]
    exact fun x hx => h.sylow_normalizes_layer hx
  have hkJ : f.ker ≤ J := by
    intro k hk
    have hkτ : τ (q k)=1 := (QuotientGroup.eq_one_iff (q k)).mp hk
    obtain ⟨d,hd,hdQ⟩ := five_fixed_representative K e c
      (natural_five_cubic_fixed_cover h hnat K hKI hNK e hcL hcN hc3) k
    have hdS : (d : G) ∈ centralizer (conjugateSpanBy (layer L R) K : Set G) := by
      intro x hx
      have he := hτ d ⟨x,hx⟩
      rw [hd,show e (QuotientGroup.mk' (pCore 2 K) k)=q k from rfl,hkτ] at he
      have he' : x=(d : G)*x*(d : G)⁻¹ := he
      exact (mul_inv_eq_iff_eq_mul.mp he'.symm).symm
    have hdV := Subgroup.centralizer_le_normalizer (layer L R : Set G)
      (centralizer_le (le_conjugateSpanBy (layer L R) K) hdS)
    have hqV := h.sylow_normalizes_layer (five_core_le_sylow K hTK hdQ)
    change (k : G) ∈ normalizer (layer L R : Set G)
    have hh := (normalizer (layer L R : Set G)).mul_mem hdV hqV
    simpa only [mul_inv_cancel_left] using hh
  have hJ := sylow_and_kernel_generate P f hf hp J hPJ hkJ
  apply hKM
  intro k hk
  exact hE.normalizer_le (show k ∈ normalizer (layer L R : Set G) from
    (show (⟨k,hk⟩ : K) ∈ J from hJ ▸ mem_top _))


/-- A faithful action on the original ambient span for every specified
S5 marking. Its cubic is the original conjugation automorphism, and the
original central line is fixed pointwise by the S5 action. -/
@[expose] def NaturalFiveSpanActionData (T : Sylow 2 G) (L R K : Subgroup G) : Prop :=
  let S := conjugateSpanBy (layer L R) K
  IsElementaryAbelian 2 S ∧ layer L R ≤ S ∧ S ≤ Escape.U (T : Subgroup G) L R ∧
    ∀ e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5),
    ∀ c : G, c ∈ L → c ∈ Escape.H (T : Subgroup G) L R → orderOf c=3 →
    ∃ hcS : c ∈ normalizer (S : Set G),
    ∃ τ : Equiv.Perm (Fin 5) →* MulAut S,
      Function.Injective τ ∧
      (∀ d : (K ⊓ centralizer (zpowers c : Set G) : Subgroup G), ∀ x : S,
        (τ (e (QuotientGroup.mk' (pCore 2 K) (inclusion inf_le_left d))) x : G) =
          (d : G)*x*(d : G)⁻¹) ∧
      (∀ s, Commute (τ s) (S.normalizerMonoidHom ⟨c,hcS⟩)) ∧
      (∀ s, ∀ z : S, (z : G) ∈ ZS (T : Subgroup G) L R → τ s z=z) ∧
      (Escape.H (T : Subgroup G) L R).pCoreIn 2 ⊓ centralizer (zpowers c : Set G) ≤
        centralizer (S : Set G)

/-- The abelian branch supplies the full marked S5 action on its actual
natural-layer span, with the literal cubic action and fixed central line. -/
theorem natural_five_span_action_data
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (K : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    NaturalFiveSpanActionData T L R K := by
  let V := layer L R
  let S := conjugateSpanBy V K
  have hSU : S ≤ Escape.U (T : Subgroup G) L R := by
    have he : conjugateSpanBy V (Escape.I (T : Subgroup G) L R) =
        Escape.U (T : Subgroup G) L R := by
      rw [conjugateSpanBy_eq_iSup_conj]
      rfl
    rw [←he]
    exact conjugateSpanBy_mono le_rfl hKI
  let := h.layer_elementary
  let : IsMulCommutative S := le_centralizer_iff_isMulCommutative.mp
    (hSU.trans (hab.trans (centralizer_le hSU)))
  have helem : IsElementaryAbelian 2 S := conjugateSpanBy_elementary_of_commutative _ _
  refine ⟨helem,le_conjugateSpanBy _ _,hSU,?_⟩
  intro e c hcL hcN hc3
  have hcS : c ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,map_conjugateSpanBy,
      mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right R L hcL),
      mem_normalizer_iff_map_conj_eq.mp (hNK hcN)]
  obtain ⟨τ,hτi,hτ⟩ := natural_five_span_action_faithful h hnat hE K hKI hNK hKM e hcL hcN hc3
  have hf := natural_five_cubic_fixed_cover h hnat K hKI hNK e hcL hcN hc3
  refine ⟨hcS,τ,hτi,hτ,?_,?_,natural_five_fixed_core_centralizes_span h hnat K hKI hNK e hcL hcN hc3⟩
  · intro s
    obtain ⟨d,hd⟩ := hf s
    rw [←hd]
    dsimp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (τ _ ((S.normalizerMonoidHom ⟨c,hcS⟩) x) : G) =
      (S.normalizerMonoidHom ⟨c,hcS⟩ (τ _ x) : G)
    rw [hτ]
    change (d : G)*(c*(x : G)*c⁻¹)*(d : G)⁻¹ = c*(τ _ x : G)*c⁻¹
    rw [hτ]
    have hdc : (d : G)*c=c*d := (d.property.2 c (mem_zpowers c)).symm
    calc
      _ = ((d : G)*c)*(x : G)*((d : G)*c)⁻¹ := by group
      _ = (c*(d : G))*(x : G)*(c*(d : G))⁻¹ := by rw [hdc]
      _ = _ := by group
  · intro s z hz
    obtain ⟨d,hd⟩ := hf s
    rw [←hd]
    dsimp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom]
    apply Subtype.ext
    rw [hτ]
    exact mul_inv_eq_iff_eq_mul.mpr ((hKI d.property.1) z hz).symm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- The same original W/Z_S witness carries a faithful S5 action on its
actual ambient layer span in the remaining contained branch. -/
theorem exists_ambient_amalgam_or_five_span_action
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
                ∃ c t : G, c ∈ L ∧ c ∈ N ∧ orderOf c=3 ∧
                  t ∈ N.pCoreIn 2 ∧ orderOf t=2 ∧ c*t*c⁻¹=t ∧ t ∉ Z ∧ t ∈ centralizer (layer L R : Set G) ∧
                  t ∈ centralizer (conjugateSpanBy (layer L R)
                    ((P ⊔ N.pCoreIn 2) ⊓ centralizer (zpowers c : Set G)) : Set G))) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,ham⟩ :=
    d.exists_ambient_amalgam_or_five_fixed_layer h hnat hE hs hNS hab
  let := hZ
  let := hX
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,?_⟩
  apply ham.imp_right
  rintro ⟨hd,hno,hfixed,hobs⟩
  exact ⟨hd,hno,hfixed,natural_five_span_action_data (hn ▸ h) (hn ▸ hnat) hE
    _ hcover.1 hcover.2.1 hescape.2.1 hab,hobs⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
