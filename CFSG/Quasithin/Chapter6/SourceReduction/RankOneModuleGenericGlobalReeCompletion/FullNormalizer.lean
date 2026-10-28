module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.FullNormalizer
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Generated
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.NativeAction

/-!
# The original full-normalizer Ree extension

The native action of the whole common normalizer is inner precisely on the
original common Borel: native Borel self-normalization detects the inner
preimage. Normal-supplement gluing therefore extends this action faithfully
across both full normalizers, retaining the original parabolic and whole
Borel markings. This constructs the extension and the compatible comparison
required by the completed small-completion recognizer, for all m > 0.
The ambient order comparison for this same carrier remains a separate duty.

Source: Aschbacher–Smith 5.3.1–2 and F.4.3, printed pp.658–659,274
(`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
variable {G : Type*} [Group G]

/-- The actual full normalizers, together with coherent pure endpoint and
whole Borel markings in the forced linear/Suzuki orientation. -/
structure FullNormalizerMarking {N : Type*} [Group N]
    (L K S : Subgroup G) (R₀ C R₁ : Subgroup N)
    (β : RankTwoAmalgam R₀ C R₁) where
  extension : UnitaryNonbinary.SourceExtension R₀ R₁
  left_le : ChapterF.Source.parabolic ![L,K] S 0 ≤ normalizer (L : Set G)
  right_le : ChapterF.Source.parabolic ![L,K] S 1 ≤ normalizer (K : Set G)
  pure : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) β
  full : RankTwoAmalgam.Iso
    (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (K : Set G)))
    extension.amalgam
  left_marking : ∀ x, (full.left (inclusion left_le x)).val = MulAut.conj (pure.left x).val
  right_marking : ∀ x, (full.right (inclusion right_le x)).val = MulAut.conj (pure.right x).val
  middle_marking : ∀ b, (full.middle (inclusion
    (le_inf (inf_le_left.trans left_le) (inf_le_right.trans right_le)) b)).val =
      MulAut.conj (pure.middle b).val

/-- The same marked diagram for the native general Ree pair. -/
abbrev ReeNormalizerMarking (L K S : Subgroup G) (m : ℕ) :=
  FullNormalizerMarking L K S (ReeF4.Parabolics.parabolic m .linear)
    (ReeF4.Parabolics.borel m) (ReeF4.Parabolics.parabolic m .suzuki)
    (ReeFour.amalgam m).reverse

private theorem conjugation_transport {N : Type*} [Group N]
    (P : Subgroup G) (R : Subgroup N) (e : P ≃* R)
    (a : MulAut R) (f : MulAut N) (d : G)
    (hc : ∀ x, (e.symm (a (e x))).val = d * x.val * d⁻¹)
    (hf : ∀ x : R, f x.val = (a x).val) (x : P) :
    ∃ hx : d*x.val*d⁻¹ ∈ P, (e ⟨d*x.val*d⁻¹,hx⟩).val = f (e x).val := by
  have hh := hc x
  refine ⟨hh ▸ (e.symm (a (e x))).property, ?_⟩
  have he : (⟨d*x.val*d⁻¹,hh ▸ (e.symm (a (e x))).property⟩ : P) =
      e.symm (a (e x)) := Subtype.ext hh.symm
  rw [he,e.apply_symm_apply,hf]

private theorem preserved_subgroup {X : Type*} [Group X]
    (R : Subgroup X) (f : MulAut X) (a : MulAut R)
    (hf : ∀ x : R, f x.val = (a x).val) : R.map f.toMonoidHom = R := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change f x ∈ R
    rw [hf ⟨x,hx⟩]
    exact (a ⟨x,hx⟩).property
  · intro x hx
    refine ⟨(a.symm ⟨x,hx⟩).val,(a.symm ⟨x,hx⟩).property,?_⟩
    exact (hf (a.symm ⟨x,hx⟩)).trans
      (congrArg Subtype.val (a.apply_symm_apply ⟨x,hx⟩))

private theorem action_ext {N : Type*} [Group N]
    (R₀ R₁ : Subgroup N) (hgen : R₀ ⊔ R₁ = ⊤) {f g : MulAut N}
    (hl : ∀ x : R₀, f x.val=g x.val)
    (hr : ∀ x : R₁, f x.val=g x.val) : f=g := by
  have h : R₀ ⊔ R₁ ≤ f.toMonoidHom.eqLocus g.toMonoidHom := sup_le
        (fun x hx => hl ⟨x,hx⟩) (fun x hx => hr ⟨x,hx⟩)
  rw [hgen] at h
  exact MulEquiv.ext (fun x => h (mem_top x))

private theorem inner_preimage {N : Type*} [Group N]
    (P Q I C : Subgroup G) (R₀ B₀ R₁ : Subgroup N)
    (hgen : R₀ ⊔ R₁ = ⊤) (hBn : normalizer (B₀ : Set N) = B₀)
    (hCI : C ≤ I) (hCP : C ≤ P) (hCQ : C ≤ Q)
    (eP : P ≃* R₀)
    (eQ : Q ≃* R₁)
    (eC : C ≃* B₀)
    (hPC : ∀ c : C, (eP ⟨c.val,hCP c.property⟩).val = (eC c).val)
    (hQC : ∀ c : C, (eQ ⟨c.val,hCQ c.property⟩).val = (eC c).val)
    (σ : I →* MulAut (N)) (hσ : Function.Injective σ)
    (aB : I → MulAut (B₀))
    (hsb : ∀ (g : I) (x : B₀), σ g x.val = (aB g x).val)
    (hcP : ∀ (g : I) (x : P), ∃ hx : g.val*x.val*g.val⁻¹ ∈ P,
      (eP ⟨_,hx⟩).val = σ g (eP x).val)
    (hcQ : ∀ (g : I) (x : Q), ∃ hx : g.val*x.val*g.val⁻¹ ∈ Q,
      (eQ ⟨_,hx⟩).val = σ g (eQ x).val) :
    (∀ c : C, σ (inclusion hCI c) = MulAut.conj (eC c).val) ∧
      (∀ g : I, σ g ∈ UnitaryNonbinary.inner (N) ↔ g.val ∈ C) := by
  have ha (c : C) : σ (inclusion hCI c) = MulAut.conj (eC c).val := by
    apply action_ext R₀ R₁ hgen
    · intro x
      let y := eP.symm x
      obtain ⟨hy,heq⟩ := hcP (inclusion hCI c) y
      change (eP (⟨c.val,hCP c.property⟩ * y *
        (⟨c.val,hCP c.property⟩ : P)⁻¹)).val = _ at heq
      rw [map_mul,map_mul,map_inv] at heq
      simpa only [y,eP.apply_symm_apply,Subgroup.coe_mul,Subgroup.coe_inv,hPC,
        MulAut.conj_apply] using heq.symm
    · intro x
      let y := eQ.symm x
      obtain ⟨hy,heq⟩ := hcQ (inclusion hCI c) y
      change (eQ (⟨c.val,hCQ c.property⟩ * y *
        (⟨c.val,hCQ c.property⟩ : Q)⁻¹)).val = _ at heq
      rw [map_mul,map_mul,map_inv] at heq
      simpa only [y,eQ.apply_symm_apply,Subgroup.coe_mul,Subgroup.coe_inv,hQC,
        MulAut.conj_apply] using heq.symm
  have hi (g : I) : σ g ∈ UnitaryNonbinary.inner (N) ↔ g.val ∈ C := by
    constructor
    · rintro ⟨z,hz⟩
      have hb := preserved_subgroup (B₀) (σ g) (aB g) (hsb g)
      rw [←hz] at hb
      have hzn : z ∈ normalizer (B₀ : Set (N)) := by
        apply mem_normalizer_iff.mpr
        intro x
        constructor
        · intro hx
          exact hb.le ⟨x,hx,rfl⟩
        · intro hx
          obtain ⟨y,hy,heq⟩ := hb.ge hx
          have hyx : y=x := (MulAut.conj z).injective heq
          exact hyx ▸ hy
      have hzb := hBn.le hzn
      let c : C := eC.symm ⟨z,hzb⟩
      have hsc : σ (inclusion hCI c) = σ g := (ha c).trans (by rw [eC.apply_symm_apply]; exact hz)
      have heq := congrArg Subtype.val (hσ hsc)
      exact heq ▸ c.property
    · intro hg
      rw [←show inclusion hCI (⟨g.val,hg⟩ : C) = g from Subtype.ext rfl,ha]
      exact ⟨_,rfl⟩
  exact ⟨ha,hi⟩

private theorem marking_of_lift {N : Type*} [Group N]
    (R₀ B₀ R₁ : Subgroup N) (hB₀ : B₀ ≤ R₀) (hB₁ : B₀ ≤ R₁)
    (hgen : R₀ ⊔ R₁ = ⊤) (hoverlap : R₀ ⊓ R₁ = B₀)
    (hconj : Function.Injective (MulAut.conj : N →* MulAut N))
    (L K S : Subgroup G)
    (β : RankTwoAmalgam R₀ B₀ R₁)
    (hβl : ∀ b, (β.left b).val = b.val)
    (hβr : ∀ b, (β.right b).val = b.val)
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) β)
    (hPM : ChapterF.Source.parabolic ![L,K] S 0 ≤ normalizer (L : Set G))
    (hQM : ChapterF.Source.parabolic ![L,K] S 1 ≤ normalizer (K : Set G))
    (hPI : ∀ i, ChapterF.Source.parabolic ![L,K] S i ⊓
      (normalizer (L : Set G) ⊓ normalizer (K : Set G)) =
      ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1)
    (hprod₁ : ∀ x ∈ normalizer (L : Set G), ∃ p ∈ ChapterF.Source.parabolic ![L,K] S 0,
      ∃ b ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G), x = p*b)
    (hprod₂ : ∀ x ∈ normalizer (K : Set G), ∃ p ∈ ChapterF.Source.parabolic ![L,K] S 1,
      ∃ b ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G), x = p*b)
    (σ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* MulAut (N))
    (hσ : Function.Injective σ)
    (hs : ∀ g, (R₀).map (σ g).toMonoidHom =
        R₀ ∧
      (R₁).map (σ g).toMonoidHom =
        R₁)
    (hi : ∀ g, σ g ∈ UnitaryNonbinary.inner (N) ↔
      g.val ∈ ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1)
    (ha : ∀ c : (ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1 : Subgroup G),
      σ (inclusion (le_inf (inf_le_left.trans hPM) (inf_le_right.trans hQM)) c) =
        MulAut.conj (e.middle c).val)
    (hcP : ∀ g (x : ChapterF.Source.parabolic ![L,K] S 0),
      ∃ hx : g.val*x.val*g.val⁻¹ ∈ ChapterF.Source.parabolic ![L,K] S 0,
        (e.left ⟨_,hx⟩).val = σ g (e.left x).val)
    (hcQ : ∀ g (x : ChapterF.Source.parabolic ![L,K] S 1),
      ∃ hx : g.val*x.val*g.val⁻¹ ∈ ChapterF.Source.parabolic ![L,K] S 1,
        (e.right ⟨_,hx⟩).val = σ g (e.right x).val) :
    Nonempty (FullNormalizerMarking L K S R₀ B₀ R₁ β) := by
  let P := ChapterF.Source.parabolic ![L,K] S
  let M₁ := normalizer (L : Set G)
  let M₂ := normalizer (K : Set G)
  let I := M₁ ⊓ M₂
  let C := P 0 ⊓ P 1
  have hCI : C ≤ I := le_inf (inf_le_left.trans hPM) (inf_le_right.trans hQM)
  have hPC (c : C) : (e.left ⟨c.val,c.property.1⟩).val = (e.middle c).val :=
    (congrArg Subtype.val (e.left_commutes c)).trans (hβl _)
  have hQC (c : C) : (e.right ⟨c.val,c.property.2⟩).val = (e.middle c).val :=
    (congrArg Subtype.val (e.right_commutes c)).trans (hβr _)
  obtain ⟨E,f,hfP,hfQ,hfI⟩ := GeneralReeFour.extension_of_lift hconj R₀ B₀ R₁ hB₀ hB₁ hgen hoverlap
    (P 0) (P 1) M₁ M₂ I C hPM hQM inf_le_left inf_le_right hCI
    (hPI 0) (hPI 1) hprod₁ hprod₂ e.left e.right e.middle hPC hQC σ hσ
    hs
    hi ha hcP hcQ
  have hmiddle : ∀ c : C, (f.middle (inclusion
      (le_inf (inf_le_left.trans hPM) (inf_le_right.trans hQM)) c)).val =
        MulAut.conj (e.middle c).val := by
    intro c
    exact (hfI (inclusion hCI c)).trans (ha c)
  exact ⟨E,hPM,hQM,e,f,hfP,hfQ,hmiddle⟩

private theorem marking_of_action {N : Type*} [Group N]
    (R₀ B₀ R₁ : Subgroup N) (hB₀ : B₀ ≤ R₀) (hB₁ : B₀ ≤ R₁)
    (hgen : R₀ ⊔ R₁ = ⊤) (hoverlap : R₀ ⊓ R₁ = B₀)
    (hconj : Function.Injective (MulAut.conj : N →* MulAut N))
    (hBn : normalizer (B₀ : Set N) = B₀)
    (L K S : Subgroup G) (β : RankTwoAmalgam R₀ B₀ R₁)
    (hβl : ∀ b, (β.left b).val = b.val)
    (hβr : ∀ b, (β.right b).val = b.val)
    (e : RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,K] S) β)
    (hPM : ChapterF.Source.parabolic ![L,K] S 0 ≤ normalizer (L : Set G))
    (hQM : ChapterF.Source.parabolic ![L,K] S 1 ≤ normalizer (K : Set G))
    (hPI : ∀ i, ChapterF.Source.parabolic ![L,K] S i ⊓
      (normalizer (L : Set G) ⊓ normalizer (K : Set G)) =
      ChapterF.Source.parabolic ![L,K] S 0 ⊓ ChapterF.Source.parabolic ![L,K] S 1)
    (hprod₁ : ∀ x ∈ normalizer (L : Set G), ∃ p ∈ ChapterF.Source.parabolic ![L,K] S 0,
      ∃ b ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G), x = p*b)
    (hprod₂ : ∀ x ∈ normalizer (K : Set G), ∃ p ∈ ChapterF.Source.parabolic ![L,K] S 1,
      ∃ b ∈ normalizer (L : Set G) ⊓ normalizer (K : Set G), x = p*b)
    (aL : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) → MulAut R₀)
    (aR : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) → MulAut R₁)
    (aB : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) → MulAut B₀)
    (σ : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* MulAut N)
    (hσ : Function.Injective σ)
    (hcl : ∀ g x, (e.left.symm ((aL g) (e.left x)) : G) =
      (g : G)*(x : G)*(g : G)⁻¹)
    (hcr : ∀ g x, (e.right.symm ((aR g) (e.right x)) : G) =
      (g : G)*(x : G)*(g : G)⁻¹)
    (hsl : ∀ g (x : R₀), σ g x.val=((aL g) x).val)
    (hsr : ∀ g (x : R₁), σ g x.val=((aR g) x).val)
    (hsb : ∀ g (x : B₀), σ g x.val=((aB g) x).val) :
    Nonempty (FullNormalizerMarking L K S R₀ B₀ R₁ β) := by
  let P := ChapterF.Source.parabolic ![L,K] S
  let I := normalizer (L : Set G) ⊓ normalizer (K : Set G)
  let C := P 0 ⊓ P 1
  have hCI : C ≤ I := (hPI 0).ge.trans inf_le_right
  have hcP (g : I) (x : P 0) : ∃ hx : g.val*x.val*g.val⁻¹ ∈ P 0,
      (e.left ⟨_,hx⟩).val = σ g (e.left x).val :=
    conjugation_transport (P 0) _ e.left (aL g) (σ g) g.val (hcl g) (hsl g) x
  have hcQ (g : I) (x : P 1) : ∃ hx : g.val*x.val*g.val⁻¹ ∈ P 1,
      (e.right ⟨_,hx⟩).val = σ g (e.right x).val :=
    conjugation_transport (P 1) _ e.right (aR g) (σ g) g.val (hcr g) (hsr g) x
  have hPC (c : C) : (e.left ⟨c.val,c.property.1⟩).val = (e.middle c).val :=
    (congrArg Subtype.val (e.left_commutes c)).trans (hβl _)
  have hQC (c : C) : (e.right ⟨c.val,c.property.2⟩).val = (e.middle c).val :=
    (congrArg Subtype.val (e.right_commutes c)).trans (hβr _)
  obtain ⟨ha,hi⟩ := inner_preimage (P 0) (P 1) I C R₀ B₀ R₁
    hgen hBn hCI inf_le_left inf_le_right
    e.left e.right e.middle hPC hQC σ hσ (fun g => (aB g)) hsb hcP hcQ
  exact marking_of_lift R₀ B₀ R₁ hB₀ hB₁ hgen hoverlap hconj L K S β hβl hβr e
    hPM hQM hPI hprod₁ hprod₂ σ hσ
    (fun g => ⟨preserved_subgroup _ _ _ (hsl g),preserved_subgroup _ _ _ (hsr g)⟩)
    hi ha hcP hcQ

private theorem native_generation (m : ℕ) :
    ReeF4.Parabolics.parabolic m .linear ⊔ ReeF4.Parabolics.parabolic m .suzuki = ⊤ := by
  rw [sup_comm]
  exact ReeFour.parabolics_generate m

private theorem native_overlap (m : ℕ) :
    ReeF4.Parabolics.parabolic m .linear ⊓ ReeF4.Parabolics.parabolic m .suzuki =
      ReeF4.Parabolics.borel m := by
  rw [inf_comm]
  exact ReeFour.overlap m

private theorem native_self_normalizing (m : ℕ) :
    normalizer (ReeF4.Parabolics.borel m : Set (ReeF4.Model m)) =
      ReeF4.Parabolics.borel m := by
  rw [←ReeFour.sylow_normalizer]
  exact (ReeFour.sylow m).normalizer_normalizer

-- Check the inclusion equations over an abstract carrier before specializing:
-- direct native reflexivity unnecessarily expands the concrete matrix group.
private theorem reverse_left_val {N : Type*} [Group N]
    (P C Q : Subgroup N) (hP : C ≤ P) (hQ : C ≤ Q) (b : C) :
    ((RankTwoAmalgam.ofSubgroups P C Q hP hQ).reverse.left b).val = b.val := rfl

private theorem reverse_right_val {N : Type*} [Group N]
    (P C Q : Subgroup N) (hP : C ≤ P) (hQ : C ≤ Q) (b : C) :
    ((RankTwoAmalgam.ofSubgroups P C Q hP hQ).reverse.right b).val = b.val := rfl

private theorem native_left_val (m : ℕ) (b : ReeF4.Parabolics.borel m) :
    ((ReeFour.amalgam m).reverse.left b).val = b.val :=
  reverse_left_val (ReeF4.Parabolics.parabolic m .suzuki) (ReeF4.Parabolics.borel m)
    (ReeF4.Parabolics.parabolic m .linear)
    (ReeF4.Parabolics.borel_le_parabolic m .suzuki)
    (ReeF4.Parabolics.borel_le_parabolic m .linear) b

private theorem native_right_val (m : ℕ) (b : ReeF4.Parabolics.borel m) :
    ((ReeFour.amalgam m).reverse.right b).val = b.val :=
  reverse_right_val (ReeF4.Parabolics.parabolic m .suzuki) (ReeF4.Parabolics.borel m)
    (ReeF4.Parabolics.parabolic m .linear)
    (ReeF4.Parabolics.borel_le_parabolic m .suzuki)
    (ReeF4.Parabolics.borel_le_parabolic m .linear) b

variable [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include d h hH hp he

/-- The original prepared Ree inputs construct a genuine simultaneous
full-normalizer extension with the entire compatible overlap. -/
theorem Preparation.ree_full_normalizer_marking :
    2*m+1 = n ∧ 0 < m ∧ Nonempty (ReeNormalizerMarking L (residual H) (sourceS L H) m) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let M₁ := normalizer (L : Set G)
  let M₂ := normalizer (residual H : Set G)
  let I := M₁ ⊓ M₂
  let C := P 0 ⊓ P 1
  have hf11 := d.hypothesisF11 h hH.1.1.2
  have hl := d.ree_normalizer_local_conditions h hH hp m he
  obtain ⟨hST,hTL,hTK,_⟩ := d.ree_full_sylow h hH hp m he
  have hTI (i : Fin 2) : (T : Subgroup G) ≤ ![L,residual H] i := by
    fin_cases i
    · exact hTL
    · exact hTK
  have hIN : I = normalizer (sourceS L H : Set G) := by
    have hn := hl.normalizer_eq_middle
    rw [inf_eq_left.mpr hTL] at hn
    rw [hST]
    exact hn.symm
  have hPM : P 0 ≤ M₁ :=
    (normal_subgroupOf_iff_le_normalizer (show L ≤ P 0 from le_sup_left.trans le_sup_left)).mp
      (hf11.local_normal_in_parabolic 0)
  have hQM : P 1 ≤ M₂ :=
    (normal_subgroupOf_iff_le_normalizer (show residual H ≤ P 1 from le_sup_left.trans le_sup_left)).mp
      (hf11.local_normal_in_parabolic 1)
  have hPI (i : Fin 2) : P i ⊓ I = C := by
    change ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓ I = C
    rw [hIN,show C = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf11]
    simpa only [hST, inf_eq_left.mpr (hTI i)] using
      (hf11.commonBorel_eq_normalizer i).symm
  have hCI : C ≤ I := (hPI 0).ge.trans inf_le_right
  have hprod₁ : ∀ x ∈ M₁, ∃ p ∈ P 0, ∃ b ∈ I, x = p*b := by
    intro x hx
    obtain ⟨p,hp,b,hb,he⟩ := hl.factor_left x hx
    exact ⟨p,(show L ≤ P 0 from le_sup_left.trans le_sup_left) hp,b,hb,he⟩
  have hprod₂ : ∀ x ∈ M₂, ∃ p ∈ P 1, ∃ b ∈ I, x = p*b := by
    intro x hx
    obtain ⟨p,hp,b,hb,he⟩ := hl.factor_right x hx
    exact ⟨p,(show residual H ≤ P 1 from le_sup_left.trans le_sup_left) hp,b,hb,he⟩
  obtain ⟨e,a,σ,hσ,hcl,hcr,hcb,hsl,hsr,hsb⟩ :=
    d.ree_native_intersection_action h hH hp m he
  obtain ⟨hmn,hm,_⟩ := d.ree_local_structure h hH.1.1.2 hp m e
  exact ⟨hmn,hm,marking_of_action
    (ReeF4.Parabolics.parabolic m .linear) (ReeF4.Parabolics.borel m)
    (ReeF4.Parabolics.parabolic m .suzuki)
    (ReeF4.Parabolics.borel_le_parabolic m .linear)
    (ReeF4.Parabolics.borel_le_parabolic m .suzuki)
    (native_generation m) (native_overlap m)
    (ReeF4.SmallCompletion.conj_injective m hm) (native_self_normalizing m)
    L (residual H) (sourceS L H) (ReeFour.amalgam m).reverse
    (native_left_val m) (native_right_val m) e
    hPM hQM hPI hprod₁ hprod₂
    (fun g => (a g).left) (fun g => (a g).right) (fun g => (a g).middle)
    σ hσ hcl hcr hsl hsr hsb⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
