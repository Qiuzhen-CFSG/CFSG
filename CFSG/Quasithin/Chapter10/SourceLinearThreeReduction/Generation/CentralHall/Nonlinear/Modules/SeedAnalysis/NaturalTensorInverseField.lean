module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorCompatibleCartan
public import Theory.SpecificGroups.SL2.SylowTorusExchange
public import Theory.FieldTheory.UnitInversion

/-!
# The original exchanger acts by inverse field action on the same Hall group

Use the common tensor-Cartan marking to carry conjugation by the chosen
original Sylow exchanger to the literal two-core quotient. It preserves
the marked Sylow and Cartan and exchanges the marked factors. Since it
preserves the full inverse diagonal B, both field factors coincide.
Thus its actual action on B, in the constructed unit coordinates, is
z -> sigma(z)^(-1). This action has two-power order and is nonidentity
for n >= 3. The exact centralizer in B is carried to sigma(z) * z = 1.

The literal Hall alternative retains the same t, B, C, both quotient
markings and full kernel. Cyclicity makes this action incompatible with
ordinary field action in any multiplicative marking of B. Constructing
that ordinary field action from the original H-model remains necessary
to exclude n > 2 and prove SourceNonnormalCentralHallAt.
Source: Aschbacher--Smith 9.2.7 and 10.2.3, pp.731--732,745,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 HallGeometry
open ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance tensorInverseFieldSeedElementary : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance tensorInverseFieldBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
variable {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
include c hn e ht htn hsep
set_option backward.isDefEq.respectTransparency false


/-- The actual same exchanger acts by one field automorphism followed by
inversion on the original B. Both torus coordinates and conjugation in G
are retained. -/
theorem original_even_same_cartan_exchanger_action
    (C : Subgroup G) (hCR : C ≤ localOrbit T L) (hBC : B.map H.subtype ≤ C)
    (htC : t ∈ normalizer (C : Set G)) (htB : t ∈ normalizer (B.map H.subtype : Set G))
    (k : OriginalTensorCartanMarking D ht n C hCR) :
    ∃ (χ : B ≃* (GaloisField 2 n)ˣ) (β : MulAut B) (σ : GaloisField 2 n ≃+* GaloisField 2 n),
      β ≠ 1 ∧ (∃ a : ℕ, β^(2^a) = 1) ∧
      (∀ (ψ : B ≃* (GaloisField 2 n)ˣ) (τ : GaloisField 2 n ≃+* GaloisField 2 n),
        ¬ ∀ b : B, ψ (β b) = Units.map τ.toMonoidHom (ψ b)) ∧
      (∀ b : B, (β b:G) = t*(b:G)*t⁻¹) ∧
      (∀ b : B, χ (β b) = (Units.map σ.toMonoidHom (χ b))⁻¹) ∧
      (∀ x : C, k.cartan (C.normalizerMonoidHom ⟨t,htC⟩ x) =
        (Units.map σ.toMonoidHom (k.cartan x).2,Units.map σ.toMonoidHom (k.cartan x).1)) ∧
      (∀ b : B, k.cartan ⟨(b:G),hBC (mem_map_of_mem H.subtype b.property)⟩ = (χ b,(χ b)⁻¹)) ∧
      C ⊓ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) =
        B.map H.subtype ∧
      (∀ b : B, Commute t (b:G) ↔ Units.map σ.toMonoidHom (χ b) * χ b = 1) ∧
      Nat.card {b : B // Commute t (b:G)} =
        Nat.card {z : (GaloisField 2 n)ˣ // Units.map σ.toMonoidHom z * z = 1} := by
  let F := GaloisField 2 n
  let R := localOrbit T L
  let q := k.quotient
  let qb : (R ⧸ pCore 2 R) ≃* (SL(2,F) × SL(2,F)) :=
    (QuotientGroup.quotientMulEquivOfEq k.kernel.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q k.surjective)
  have hqb (r : R) : qb (QuotientGroup.mk' (pCore 2 R) r) = q r := rfl
  let tR : normalizer (R : Set G) := ⟨t,le_normalizer_componentOrbit L T ht⟩
  let θ := MulAut.congr qb (normalizerQuotientAction R (pCore 2 R) tR)
  have hθ (r : R) : θ (q r) = q (R.normalizerMonoidHom tR r) := by
    rw [←hqb]
    change qb ((normalizerQuotientAction R (pCore 2 R) tR)
      (qb.symm (qb (QuotientGroup.mk' (pCore 2 R) r)))) = _
    rw [qb.symm_apply_apply]
    change qb (quotientAut (pCore 2 R) _ _) = _
    rw [quotientAut_apply_mk,hqb]
  let a := k.firstEquiv.symm.trans k.secondEquiv
  have hfirst (x : SL(2,F)) : θ (x,1) = (1,a x) := by
    obtain ⟨l,rfl⟩ := k.firstEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) x
    change θ (k.firstEquiv (QuotientGroup.mk' (pCore 2 L) l),1) = _
    rw [←k.first,hθ]
    change q (originalConjugateOrbitInclusion ht l) = _
    rw [k.second]
    simp only [a,MulEquiv.trans_apply,Function.comp_apply,MulEquiv.symm_apply_apply]
  have hU : ((Matrix.SpecialLinearGroup.upperUnipotent F).prod
      (Matrix.SpecialLinearGroup.upperUnipotent F)).map θ.toMonoidHom =
      (Matrix.SpecialLinearGroup.upperUnipotent F).prod (Matrix.SpecialLinearGroup.upperUnipotent F) := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨y,hy,rfl⟩
      obtain ⟨r,hr,rfl⟩ := k.sylow.symm ▸ hy
      change θ (q r) ∈ _
      rw [hθ,←k.sylow]
      apply mem_map_of_mem
      change t*(r:G)*t⁻¹ ∈ (T : Subgroup G)
      exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hr)
        ((T : Subgroup G).inv_mem ht)
    · rw [card_map_of_injective θ.injective]
  let j : C →* R := inclusion hCR
  let γ := C.normalizerMonoidHom ⟨t,htC⟩
  have hj (x : C) : R.normalizerMonoidHom tR (j x) = j (γ x) := rfl
  have hdiagC (x : C) : q (j x) =
      (Matrix.SpecialLinearGroup.diag2 ((k.cartan x).1:F) (Units.ne_zero _),
        Matrix.SpecialLinearGroup.diag2 ((k.cartan x).2:F) (Units.ne_zero _)) := k.diagonal x
  have hD (z : Fˣ × Fˣ) : ∃ w : Fˣ × Fˣ,
      θ (Matrix.SpecialLinearGroup.diag2 (z.1:F) z.1.ne_zero,
        Matrix.SpecialLinearGroup.diag2 (z.2:F) z.2.ne_zero) =
      (Matrix.SpecialLinearGroup.diag2 (w.1:F) w.1.ne_zero,
        Matrix.SpecialLinearGroup.diag2 (w.2:F) w.2.ne_zero) := by
    obtain ⟨x,rfl⟩ := k.cartan.surjective z
    refine ⟨k.cartan (γ x),?_⟩
    rw [←hdiagC x,hθ,hj,hdiagC]
  obtain ⟨χ,hmark,hmem,hcentral⟩ := original_even_same_cartan_hall D c n hn e ht htn hsep C hCR hBC k
  let eB := B.equivMapOfInjective H.subtype H.subtype_injective
  let β : MulAut B := MulAut.congr eB.symm
    ((B.map H.subtype).normalizerMonoidHom ⟨t,htB⟩)
  have hβ (b : B) : (β b:G) = t*(b:G)*t⁻¹ := by
    have he : eB (β b) = (B.map H.subtype).normalizerMonoidHom ⟨t,htB⟩ (eB b) := by
      change eB (eB.symm ((B.map H.subtype).normalizerMonoidHom ⟨t,htB⟩ (eB b))) = _
      exact eB.apply_symm_apply _
    exact congrArg (fun x : B.map H.subtype => (x:G)) he
  let bC (b : B) : C := ⟨(b:G),hBC (mem_map_of_mem H.subtype b.property)⟩
  have hbC (b : B) : γ (bC b) = bC (β b) := Subtype.ext (hβ b).symm
  have hB (z : Fˣ) : ∃ w : Fˣ,
      θ (Matrix.SpecialLinearGroup.diag2 (z:F) z.ne_zero,
        Matrix.SpecialLinearGroup.diag2 (↑(z⁻¹):F) (Units.ne_zero _)) =
      (Matrix.SpecialLinearGroup.diag2 (w:F) w.ne_zero,
        Matrix.SpecialLinearGroup.diag2 (↑(w⁻¹):F) (Units.ne_zero _)) := by
    obtain ⟨b,rfl⟩ := χ.surjective z
    refine ⟨χ (β b),?_⟩
    have hdiag (b : B) : q (j (bC b)) =
        (Matrix.SpecialLinearGroup.diag2 (χ b:F) (Units.ne_zero _),
          Matrix.SpecialLinearGroup.diag2 (↑((χ b)⁻¹):F) (Units.ne_zero _)) := by
      rw [hdiagC,hmark]
    rw [←hdiag,hθ,hj,hbC,hdiag]
  have hF : 2 < Nat.card F := by
    rw [GaloisField.card 2 n (by omega)]
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    norm_num at h
    omega
  obtain ⟨σ,hσ⟩ := Matrix.SpecialLinearGroup.pair_sylow_torus_exchanger_field hF θ a hfirst hU hD hB
  have hγ (x : C) : k.cartan (γ x) =
      (Units.map σ.toMonoidHom (k.cartan x).2,Units.map σ.toMonoidHom (k.cartan x).1) := by
    have hh := hσ (k.cartan x)
    rw [←hdiagC x,hθ,hj,hdiagC] at hh
    apply Prod.ext <;> apply Units.ext
    · simpa [Matrix.SpecialLinearGroup.diag2_coe'] using
        congrArg (fun p : SL(2,F) × SL(2,F) => p.1.val 0 0) hh
    · simpa [Matrix.SpecialLinearGroup.diag2_coe'] using
        congrArg (fun p : SL(2,F) × SL(2,F) => p.2.val 0 0) hh
  have hact (b : B) : χ (β b) = (Units.map σ.toMonoidHom (χ b))⁻¹ := by
    have hh := hγ (bC b)
    rw [hbC,hmark,hmark] at hh
    simpa only [map_inv] using congrArg Prod.fst hh
  have hβne : β ≠ 1 := by
    intro hb
    have hF4 : 4 < Nat.card F := by
      rw [GaloisField.card 2 n (by omega)]
      have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
      norm_num at h
      omega
    obtain ⟨z,hz⟩ := FiniteField.exists_unit_not_inverted hF4 σ
    obtain ⟨b,rfl⟩ := χ.surjective z
    have hh := hact b
    rw [hb] at hh
    exact hz (by simpa only [MulAut.one_apply,inv_inv] using (congrArg Inv.inv hh).symm)
  have hβtwo : ∃ a : ℕ, β^(2^a) = 1 := by
    obtain ⟨a,ha⟩ := T.isPGroup' ⟨t,ht⟩
    let ψ := (MulAut.congr eB.symm).toMonoidHom.comp (B.map H.subtype).normalizerMonoidHom
    have htN : (⟨t,htB⟩ : normalizer (B.map H.subtype : Set G))^(2^a) = 1 :=
      Subtype.ext (congrArg (fun x : T => (x:G)) ha)
    refine ⟨a,?_⟩
    change (ψ ⟨t,htB⟩)^(2^a) = 1
    rw [←map_pow,htN,map_one]
  have hfix (b : B) : β b = b ↔ Units.map σ.toMonoidHom (χ b) * χ b = 1 := by
    constructor
    · intro hb
      have hh := hact b
      rw [hb] at hh
      calc
        Units.map σ.toMonoidHom (χ b) * χ b =
          Units.map σ.toMonoidHom (χ b) * (Units.map σ.toMonoidHom (χ b))⁻¹ :=
            congrArg (fun z => Units.map σ.toMonoidHom (χ b) * z) hh
        _ = 1 := mul_inv_cancel _
    · intro hh
      apply χ.injective
      rw [hact,eq_inv_of_mul_eq_one_left hh,inv_inv]
  have hfixed (b : B) : Commute t (b:G) ↔ Units.map σ.toMonoidHom (χ b) * χ b = 1 := by
    rw [←hfix]
    constructor
    · intro hc
      apply Subtype.ext
      apply Subtype.ext
      rw [hβ,hc.eq,mul_inv_cancel_right]
    · intro hh
      change t*(b:G) = (b:G)*t
      exact mul_inv_eq_iff_eq_mul.mp
        ((hβ b).symm.trans (congrArg (fun x : B => (x:G)) hh))
  have hno (ψ : B ≃* Fˣ) (τ : F ≃+* F)
      (hψ : ∀ b : B, ψ (β b) = Units.map τ.toMonoidHom (ψ b)) : False := by
    apply FiniteField.inverse_field_action_not_field (F := F) _ χ β σ hact ψ τ hψ
    rw [GaloisField.card 2 n (by omega)]
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn
    norm_num at h
    omega
  exact ⟨χ,β,σ,hβne,hβtwo,hno,hβ,hact,hγ,hmark,hcentral,hfixed,
    Nat.card_congr (χ.toEquiv.subtypeEquiv hfixed)⟩


omit hn e ht htn hsep in
/-- The original Hall alternative now retains a compatible Cartan marking,
a nontrivial inverse field action of the same Sylow exchanger, and the exact
fixed subgroup on the unchanged Hall carrier. It also excludes ordinary
field action in every multiplicative marking. Constructing that action
from the original H-model remains necessary to exclude this branch. -/
theorem original_hall_conclusion_or_natural_tensor_inverse_field :
    (IsPGroup 3 B ∨ ∃ k : ℕ, Monoid.exponent B ∣ 2^k+1) ∨
      ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
            D.seed ≤ centralizer (L : Set G)) ∧
          OriginalEvenNaturalTensorAnalysis D ht n e ∧
          OriginalEvenSeedDeterminantCoordinates D ht n e ∧
          D.moduleSubgroup = D.seed ∧
          H ⊓ D.maximalLocal ≤ normalizer (D.seed : Set G) ∧
          B.map H.subtype ≤ localOrbit T L ∧ IsCyclic B ∧
          Nat.card B = 2^n-1 ∧ Monoid.exponent B = 2^n-1 ∧
          n-1 ≤ ChapterE.generationParameter H ∧ ChapterE.generationParameter H ≤ n ∧
          ∃ (C : Subgroup G) (hC : C ≤ sourceOrbitBorel T L),
            B.map H.subtype ≤ C ∧
            IsHallSubgroup OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L)) ∧
            ∃ (htC : t ∈ normalizer (C : Set G)), t ∈ normalizer (B.map H.subtype : Set G) ∧
            ∃ k : OriginalTensorCartanMarking D ht n C
              ((hC.trans (map_subtype_le _)).trans inf_le_left),
            ∃ (χ : B ≃* (GaloisField 2 n)ˣ) (β : MulAut B) (σ : GaloisField 2 n ≃+* GaloisField 2 n),
              β ≠ 1 ∧ (∃ a : ℕ, β^(2^a) = 1) ∧
              (∀ (ψ : B ≃* (GaloisField 2 n)ˣ) (τ : GaloisField 2 n ≃+* GaloisField 2 n),
                ¬ ∀ b : B, ψ (β b) = Units.map τ.toMonoidHom (ψ b)) ∧
              (∀ b : B, (β b:G) = t*(b:G)*t⁻¹) ∧
              (∀ b : B, χ (β b) = (Units.map σ.toMonoidHom (χ b))⁻¹) ∧
              (∀ x : C, k.cartan (C.normalizerMonoidHom ⟨t,htC⟩ x) =
                (Units.map σ.toMonoidHom (k.cartan x).2,Units.map σ.toMonoidHom (k.cartan x).1)) ∧
              (∀ b : B, ∃ hbC : (b:G) ∈ C, k.cartan ⟨(b:G),hbC⟩ = (χ b,(χ b)⁻¹)) ∧
              C ⊓ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) =
                B.map H.subtype ∧
              (∀ b : B, Commute t (b:G) ↔ Units.map σ.toMonoidHom (χ b) * χ b = 1) ∧
              Nat.card {b : B // Commute t (b:G)} =
                Nat.card {z : (GaloisField 2 n)ˣ // Units.map σ.toMonoidHom z * z = 1} := by
  rcases original_hall_conclusion_or_natural_tensor_exchanger D c with hh |
    ⟨t,ht,htn,n,hn,e,hsep,ha,hdet,heq,hseed,hBR,hcyc,hcard,hexp,hlo,hhi,C,hBC,hC,hHall,⟨f⟩,htC,htB⟩
  · exact Or.inl hh
  · have hodd : Odd (Nat.card C) := by
      have hh := OddHall.odd_hall_odd hHall
      rwa [Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv] at hh
    obtain ⟨k⟩ := original_even_same_cartan_coordinates D c n hn e ht htn hsep C hC
      hodd (Nat.card_congr f.toEquiv)
    obtain ⟨χ,β,σ,hne,hpow,hno,hβ,hact,hγ,hmark,hcentral,hfixed,hcount⟩ :=
      original_even_same_cartan_exchanger_action D c n hn e ht htn hsep C _ hBC htC htB k
    exact Or.inr ⟨t,ht,htn,n,hn,e,hsep,ha,hdet,heq,hseed,hBR,hcyc,hcard,hexp,hlo,hhi,
      C,hC,hBC,hHall,htC,htB,k,χ,β,σ,hne,hpow,hno,hβ,hact,hγ,
      fun b => ⟨hBC (mem_map_of_mem H.subtype b.property),hmark b⟩,hcentral,hfixed,hcount⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
