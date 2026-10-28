module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.Basic
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.PairRecognition.Plane
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.PairRecognition.Model

/-!
# Natural blocks from odd-core conjugate pairs

A rank-one minimal best offender has order two and moves one binary dimension.
For a noncentral odd-core conjugator, the generating involution and its
conjugate have nonidentity odd-order product. The binary dihedral splitting
therefore supplies a plane support and its fixed complement. The restricted
action is faithful, and its two distinct involutions identify it with the
actual SL₂(2) natural action. The literal intersection with the ambient odd
core has odd order dividing six and is nontrivial, hence has order three;
its support contains the product support and is exactly the pair support.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, 9.3.3 and the
splitting argument of 9.3.6, printed pp.241–242 and245, PDF pp.254–255 and258
of `refs/original/kurzweil.pdf`. Left conjugation replaces the source's x by
its inverse. Solvability and the ambient two-core assumption are unnecessary
once the rank-one offender and the noncentral odd-core conjugator are given.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
namespace PairRecognition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [Finite G] [FiniteDimensional (ZMod 2) V]

private lemma pair_involutions (hρ : Function.Injective ρ) {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hrank : rank A = 1)
    {x : G} (hx : x ∈ pPrimeCore 2 G) (hxc : x ∉ centralizer (A : Set G)) :
    ∃ t u : G, A = zpowers t ∧ A.map (MulAut.conj x).toMonoidHom = zpowers u ∧
      t * t = 1 ∧ u * u = 1 ∧ t ≠ 1 ∧ u ≠ 1 ∧ t ≠ u ∧
      t * u ≠ 1 ∧ t * u ∈ pPrimeCore 2 G ∧ Odd (orderOf (t * u)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (zpowers t)) = 1 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (zpowers u)) = 1 := by
  have hcard := minimal_card ρ hA hrank
  obtain ⟨a, ha, hall⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
  let t : G := a
  let u : G := x * t * x⁻¹
  have htgen : A = zpowers t := by
    have he := congrArg (fun B : Subgroup A => B.map A.subtype)
      (zpowers_eq_top_of_prime_card hcard ha)
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype, subtype_apply, t] using he.symm
  have hugen : A.map (MulAut.conj x).toMonoidHom = zpowers u := by
    rw [htgen, MonoidHom.map_zpowers]
    rfl
  have ht : t * t = 1 := by
    have he : a ^ 2 = 1 := hcard ▸ pow_card_eq_one'
    exact congrArg Subtype.val (show a * a = 1 by simpa only [pow_two] using he)
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hu : u * u = 1 := by
    change (x * t * x⁻¹) * (x * t * x⁻¹) = 1
    calc
      _ = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht, mul_one, mul_inv_cancel]
  have htn : t ≠ 1 := fun he => ha (Subtype.ext he)
  have hun : u ≠ 1 := by
    intro he
    apply htn
    have he' := congrArg (fun z => x⁻¹ * z * x) he
    simpa [u, mul_assoc] using he'
  have htu : t ≠ u := by
    intro he
    apply hxc
    apply mem_centralizer_iff.mpr
    intro b hb
    by_cases hb1 : b = 1
    · simp [hb1]
    · have hb' : (⟨b, hb⟩ : A) = a := hall ⟨b, hb⟩ (fun h => hb1 (congrArg Subtype.val h))
      have hbt : b = t := congrArg Subtype.val hb'
      rw [hbt, he]
      change (x * t * x⁻¹) * x = x * u
      rw [← he]
      group
  have hprod : t * u ≠ 1 := by
    intro he
    apply htu
    have he' := congrArg (fun z => t * z) he
    simpa only [← mul_assoc, ht, one_mul, mul_one] using he'.symm
  have hmem : t * u ∈ pPrimeCore 2 G := by
    have hconj := (inferInstance : (pPrimeCore 2 G).Normal).conj_mem x hx t
    have hh := (pPrimeCore 2 G).mul_mem hconj ((pPrimeCore 2 G).inv_mem hx)
    simpa only [hti, mul_assoc, u] using hh
  have hodd : Odd (orderOf (t * u)) :=
    ((pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right
      ((pPrimeCore 2 G).orderOf_dvd_natCard hmem)).odd_of_left
  refine ⟨t, u, htgen, hugen, ht, hu, htn, hun, htu, hprod, hmem, hodd, ?_, ?_⟩
  · rw [← htgen]
    exact minimal_moved_finrank ρ hρ hA hrank
  · rw [← hugen]
    exact minimal_moved_finrank ρ hρ (hA.map_conj ρ x) (by rwa [rank_map_conj])

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private lemma support_stable (E : Subgroup G) (g : E) :
    ∀ v ∈ subspaceCommutator ρ ⊤ E, ρ g v ∈ subspaceCommutator ρ ⊤ E := by
  have hle : subspaceCommutator ρ ⊤ E ≤ (subspaceCommutator ρ ⊤ E).comap (ρ g) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, w, _, rfl⟩
    change ρ g (ρ a w - w) ∈ subspaceCommutator ρ ⊤ E
    have hga : ρ ((g : G) * a) w - w ∈ subspaceCommutator ρ ⊤ E :=
      Submodule.subset_span ⟨(g : G) * a, E.mul_mem g.property ha, w, Submodule.mem_top, rfl⟩
    have hg : ρ g w - w ∈ subspaceCommutator ρ ⊤ E :=
      Submodule.subset_span ⟨g, g.property, w, Submodule.mem_top, rfl⟩
    simpa only [map_sub, map_mul, Module.End.mul_apply, sub_sub_sub_cancel_right] using
      (subspaceCommutator ρ ⊤ E).sub_mem hga hg
  exact fun _ hv => hle hv

omit [Finite G] in
private lemma support_model (hρ : Function.Injective ρ) (E : Subgroup G)
    (hc : IsCompl (subspaceCommutator ρ ⊤ E) (fixedSpace ρ E))
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ E) = 2)
    (t u : E) (ht : t * t = 1) (hu : u * u = 1)
    (htn : t ≠ 1) (hun : u ≠ 1) (htu : t ≠ u) :
    ∃ e : E ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      ∃ f : subspaceCommutator ρ ⊤ E ≃ₗ[ZMod 2] (Fin 2 → ZMod 2),
        ∀ (g : E) (v : subspaceCommutator ρ ⊤ E), ρ (g : G) (v : V) =
          (f.symm (Representation.specialLinearNatural 2 (e g) (f v)) : V) := by
  let W := subspaceCommutator ρ ⊤ E
  let σ := Representation.subrepresentation (ρ.comp E.subtype) W (fun g => support_stable ρ E g)
  have hf : Function.Injective σ := by
    intro g h he
    apply Subtype.ext
    apply hρ
    ext v
    obtain ⟨w, hw, c, hc', rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ W ⊔ fixedSpace ρ E by rw [hc.sup_eq_top]; exact Submodule.mem_top)
    have hew := congrArg (fun f : Module.End (ZMod 2) W => (f ⟨w, hw⟩ : V)) he
    change ρ g w = ρ h w at hew
    simp only [map_add, hew, show ρ g c = c from hc' g, show ρ h c = c from hc' h]
  obtain ⟨e, f, hact⟩ := exists_natural_model σ hf hd t u ht hu htn hun htu
  refine ⟨e, f, ?_⟩
  intro g v
  have he : σ g v = f.symm (Representation.specialLinearNatural 2 (e g) (f v)) := by
    apply f.injective
    rw [f.apply_symm_apply]
    exact hact g v
  exact congrArg Subtype.val he

end PairRecognition
open PairRecognition
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The literal odd-core conjugate pair is a natural SL₂(2) block.
Only the rank-one and faithful-action consequences of the ambient solvable
hypotheses are needed for this step. -/
theorem pairData_nonempty [Finite G] [FiniteDimensional (ZMod 2) V]
    (hρ : Function.Injective ρ) {A : Subgroup G}
    (hA : IsMinimalBestOffender ρ A) (hrank : rank A = 1)
    {x : G} (hx : x ∈ pPrimeCore 2 G) (hxc : x ∉ centralizer (A : Set G)) :
    Nonempty (PairData ρ A x) := by
  obtain ⟨t, u, hAgen, hBgen, ht, hu, htn, hun, htu, hne, hmem, hodd, hdt, hdu⟩ :=
    pair_involutions ρ hρ hA hrank hx hxc
  let E := conjugatePair A x
  have hE : E = zpowers t ⊔ zpowers u := by
    change A ⊔ A.map (MulAut.conj x).toMonoidHom = _
    rw [hBgen, hAgen]
  have htE : t ∈ E := hE ▸ (le_sup_left : zpowers t ≤ zpowers t ⊔ zpowers u) (mem_zpowers t)
  have huE : u ∈ E := hE ▸ (le_sup_right : zpowers u ≤ zpowers t ⊔ zpowers u) (mem_zpowers u)
  have hpE : t * u ∈ E := E.mul_mem htE huE
  have hlinear := odd_pair_plane ρ hρ t u ht hu hne hodd hdt hdu
  change subspaceCommutator ρ ⊤ (zpowers (t * u)) =
      subspaceCommutator ρ ⊤ (zpowers t ⊔ zpowers u) ∧ _ at hlinear
  rw [← hE] at hlinear
  obtain ⟨e, f, hact⟩ := support_model ρ hρ E hlinear.2.2 hlinear.2.1
    ⟨t, htE⟩ ⟨u, huE⟩ (Subtype.ext ht) (Subtype.ext hu)
    (fun he => htn (congrArg Subtype.val he)) (fun he => hun (congrArg Subtype.val he))
    (fun he => htu (congrArg Subtype.val he))
  have hcardE : Nat.card E = 6 := (Nat.card_congr e.toEquiv).trans sl_card
  let K := E ⊓ pPrimeCore 2 G
  have hcardK : Nat.card K = 3 := by
    have hdvd : Nat.card K ∣ 6 := hcardE ▸ card_dvd_of_le (show K ≤ E from inf_le_left)
    have hKodd : Odd (Nat.card K) :=
      ((pPrimeCore_coprime_card (p := 2) (G := G)).of_dvd_right
        (card_dvd_of_le (show K ≤ pPrimeCore 2 G from inf_le_right))).odd_of_left
    have hKne : K ≠ ⊥ := by
      intro he
      have hm : t * u ∈ K := ⟨hpE, hmem⟩
      rw [he, mem_bot] at hm
      exact hne hm
    have hlo := K.one_lt_card_iff_ne_bot.mpr hKne
    have hhi := Nat.le_of_dvd (by decide : 0 < 6) hdvd
    interval_cases hk : Nat.card K <;> simp_all [Nat.odd_iff]
  refine ⟨⟨e, f, hact, hlinear.2.2, hcardK, ?_⟩⟩
  apply le_antisymm (moved_mono ρ le_rfl inf_le_left)
  rw [← hlinear.1]
  exact moved_mono ρ le_rfl (zpowers_le.mpr ⟨hpE, hmem⟩)

end CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
