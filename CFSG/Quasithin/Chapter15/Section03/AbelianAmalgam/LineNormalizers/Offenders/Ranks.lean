module

public import Stellmacher.MaxElementaryOffenderEquality
public import Theory.ElementaryAbelian.BinaryQuotientRank
public import Theory.Representation.BinaryOffender.Basic
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The two-image rank calculation for the line offender

Write `U = V_E`, let `Q` denote the temporary core, and let `f` be the faithful
conjugation quotient on `U`. For a maximum elementary subgroup `A`, this module
proves `C_U(A) = A ∩ U`, counts both actual images of `A`, and compares `A` with
the elementary subgroup `U C_A(U)`. Only `C_A(U) ≤ Q` is required; no assertion
that the whole centralizer is a two-group is used.

The correction term is the rank of the actual quotient `C_U(B)/C_U(A)`, where
`B = A ∩ Q`. The transvection identity and the paired fixed-space comparison
remain explicit geometric inputs here. The latter is discharged from an actual
quotient map in `PairedSection`. The resulting weak offender contains a best
(FF-star) offender by B.1.4; bestness of the entire image needs a further argument.

The Sylow-selection theorem retains the maximum-family comparison witness.
In particular it cannot identify `J(C_G(E)) ∩ H` with `J(C_H(E))` merely by
changing the local group to the temporary normalizer `H`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.67,
printed pp.1153–1154, PDF pp.1170–1171; Definitions B.1.2–3, printed p.68.
-/

@[expose] public section
open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders

variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- Binary dimension of the actual quotient `U / (C ∩ U)`, via its relative index. -/
noncomputable def quotientRank (U C : Subgroup G) : ℕ := Nat.log 2 (C.relIndex U)

/-- The index convention equals the vector-space dimension of the actual quotient. -/
theorem quotientRank_eq_finrank (U C : Subgroup G) [IsElementaryAbelian 2 U] :
    quotientRank U C = Module.finrank (ZMod 2) (Additive (U ⧸ C.subgroupOf U)) :=
  U.log_relIndex_eq_quotient_finrank C

private theorem card_eq_pow_rank {K : Type*} [Group K] (A : Subgroup K) [Finite A]
    (hA : IsPGroup 2 A) :
    Nat.card A = 2 ^ rank A := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  simp only [rank, hn, Nat.log_pow Nat.one_lt_two]

/-- Rank additivity for the subgroup and its actual quotient. -/
theorem quotientRank_add_rank (U C : Subgroup G) [IsElementaryAbelian 2 U]
    (hCU : C ≤ U) : quotientRank U C + rank C = rank U := by
  have he : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le hCU
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) C U bot_le hCU
  simp only [relIndex_bot_left] at hc
  rw [card_eq_pow_rank C he.isPGroup, card_eq_pow_rank U
    (IsElementaryAbelian.isPGroup 2 U),
    U.relIndex_eq_two_pow_quotient_finrank C, ← pow_add] at hc
  have hh := Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  rw [quotientRank_eq_finrank]
  omega

/-- Rank-nullity for the actual restriction of a homomorphism to an elementary subgroup. -/
theorem rank_kernel_add_image (A : Subgroup G) [IsElementaryAbelian 2 A]
    (f : G →* H) : rank (A ⊓ f.ker) + rank (A.map f) = rank A := by
  let _ : Finite (A.map f) := ((Set.toFinite (A : Set G)).image f).to_subtype
  have hk : IsElementaryAbelian 2 (A ⊓ f.ker : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have hi : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (f.ker ⊓ A) A bot_le inf_le_right
  simp only [relIndex_bot_left, inf_relIndex_right, relIndex_ker] at hc
  rw [inf_comm, card_eq_pow_rank _ hk.isPGroup,
    card_eq_pow_rank _ hi.isPGroup, card_eq_pow_rank _ (IsElementaryAbelian.isPGroup 2 A),
    ← pow_add] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc

/-- The source identity `m(Ȧ) + m(B̂) + m(D) = m(A)`. Only `D ≤ Q` is needed. -/
theorem rank_two_images (A Q U : Subgroup G) [Q.Normal]
    [IsElementaryAbelian 2 A] (f : G →* H)
    (hker : f.ker = centralizer (U : Set G)) (hkerQ : A ⊓ f.ker ≤ Q) :
    rank (A.map (QuotientGroup.mk' Q)) + rank ((A ⊓ Q).map f) +
      rank (A ⊓ centralizer (U : Set G)) = rank A := by
  let _ : IsElementaryAbelian 2 (A ⊓ Q : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have h₁ := rank_kernel_add_image A (QuotientGroup.mk' Q)
  have h₂ := rank_kernel_add_image (A ⊓ Q) f
  rw [QuotientGroup.ker_mk'] at h₁
  have hk : (A ⊓ Q) ⊓ f.ker = A ⊓ f.ker := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · exact le_inf (le_inf inf_le_left hkerQ) inf_le_right
  rw [hk, hker] at h₂
  omega

/-- Maximal elementary order forces `C_U(A) = A ∩ U`. -/
theorem max_fixed_eq_inf (S U A : Subgroup G) [IsElementaryAbelian 2 U]
    (hU : U ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    U ⊓ centralizer (A : Set G) = A ⊓ U := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 (U ⊓ centralizer (A : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  apply le_antisymm
  · exact le_inf (maxElementary_contains_elementary_centralizer S A _ hA
      (inf_le_left.trans hU) inf_le_right) inf_le_left
  · exact le_inf inf_le_right (inf_le_left.trans A.le_centralizer)

/-- The elementary replacement `D U` has rank `m(D) + m(U/C_U(A))`. -/
theorem replacement_rank (S U A : Subgroup G) [IsElementaryAbelian 2 U]
    (hU : U ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    rank ((A ⊓ centralizer (U : Set G)) ⊔ U) =
      rank (A ⊓ centralizer (U : Set G)) + quotientRank U (U ⊓ centralizer (A : Set G)) := by
  let D := A ⊓ centralizer (U : Set G)
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le inf_le_left
  let _ : IsElementaryAbelian 2 (D ⊔ U : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp inf_le_right)
  let _ : IsElementaryAbelian 2 (D ⊓ U : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes D U
    ((le_centralizer_iff.mp (show D ≤ centralizer (U : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _))
  rw [card_eq_pow_rank _ (IsElementaryAbelian.isPGroup 2 D),
    card_eq_pow_rank _ (IsElementaryAbelian.isPGroup 2 U),
    card_eq_pow_rank _ (IsElementaryAbelian.isPGroup 2 (D ⊓ U : Subgroup G)),
    card_eq_pow_rank _ (IsElementaryAbelian.isPGroup 2 (D ⊔ U : Subgroup G)),
    ← pow_add, ← pow_add] at hc
  have hr := Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  have hi : D ⊓ U = U ⊓ centralizer (A : Set G) := by
    rw [max_fixed_eq_inf S U A hU hA]
    apply le_antisymm
    · exact inf_le_inf inf_le_left le_rfl
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans U.le_centralizer)) inf_le_right
  rw [hi] at hr
  have hq := quotientRank_add_rank U (U ⊓ centralizer (A : Set G)) inf_le_left
  change rank (D ⊔ U) = rank D + _
  omega

/-- Maximality compared with `D U` gives the first displayed inequality on p.1153. -/
theorem displayed_first_bound (S U A Q : Subgroup G) [IsElementaryAbelian 2 U]
    [Q.Normal] (hU : U ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (f : G →* H) (hker : f.ker = centralizer (U : Set G)) (hkerQ : A ⊓ f.ker ≤ Q) :
    rank (A.map (QuotientGroup.mk' Q)) + rank ((A ⊓ Q).map f) ≥
      quotientRank U (U ⊓ centralizer (A : Set G)) := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let D := A ⊓ centralizer (U : Set G)
  let _ : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le inf_le_left
  have he : IsElementaryAbelian 2 (D ⊔ U : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp inf_le_right)
  have hm : rank (D ⊔ U) ≤ rank A := Nat.log_mono_right
    (hA.2.2 _ (sup_le (inf_le_left.trans hA.1) hU) he)
  have hr := replacement_rank S U A hU hA
  have ha := rank_two_images A Q U f hker hkerQ
  change rank (D ⊔ U) = rank D + _ at hr
  change _ + rank D = _ at ha
  omega

/-- The correction term is the dimension of `C_U(B)/C_U(A)`, not an arbitrary number. -/
theorem fixed_quotientRank_add (U A B : Subgroup G) [IsElementaryAbelian 2 U]
    (hBA : B ≤ A) :
    quotientRank U (U ⊓ centralizer (B : Set G)) +
      quotientRank (U ⊓ centralizer (B : Set G)) (U ⊓ centralizer (A : Set G)) =
        quotientRank U (U ⊓ centralizer (A : Set G)) := by
  let _ : IsElementaryAbelian 2 (U ⊓ centralizer (B : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have h₁ := quotientRank_add_rank U (U ⊓ centralizer (B : Set G)) inf_le_left
  have h₂ := quotientRank_add_rank U (U ⊓ centralizer (A : Set G)) inf_le_left
  have h₃ := quotientRank_add_rank (U ⊓ centralizer (B : Set G))
    (U ⊓ centralizer (A : Set G)) (inf_le_inf_left U (centralizer_le hBA))
  omega

/-- The two bounds on p.1154, once the core-action dimension has been established. -/
theorem displayed_rank_inequalities (S U A Q : Subgroup G) [IsElementaryAbelian 2 U]
    [Q.Normal] (hU : U ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (f : G →* H) (hker : f.ker = centralizer (U : Set G)) (hkerQ : A ⊓ f.ker ≤ Q)
    (hcore : quotientRank U (U ⊓ centralizer ((A ⊓ Q : Subgroup G) : Set G)) =
      2 * rank ((A ⊓ Q).map f)) :
    let N := quotientRank (U ⊓ centralizer ((A ⊓ Q : Subgroup G) : Set G))
      (U ⊓ centralizer (A : Set G))
    rank ((A ⊓ Q).map f) + N ≤ rank (A.map (QuotientGroup.mk' Q)) ∧
      quotientRank U (U ⊓ centralizer (A : Set G)) + N ≤
        2 * rank (A.map (QuotientGroup.mk' Q)) := by
  have hbound := displayed_first_bound S U A Q hU hA f hker hkerQ
  have hsplit := fixed_quotientRank_add U A (A ⊓ Q) inf_le_left
  rw [hcore] at hsplit
  dsimp only
  constructor <;> omega

/-- Sylow conjugacy selects a maximum elementary subgroup with nonidentity quotient image.
The comparison witness connects the two maximum families; it does not assume the selected image. -/
theorem exists_max_nontrivial_image (C Q : Subgroup G) [Q.Normal]
    (P : Sylow 2 G) (hJ : ¬ elementaryAbelianMaxJ C ≤ Q)
    (hcompare : ∃ B ∈ elementaryAbelianMaxSubgroups (P : Subgroup G), B ≤ C) :
    ∃ A ∈ elementaryAbelianMaxSubgroups (P : Subgroup G),
      A.map (QuotientGroup.mk' Q) ≠ ⊥ := by
  classical
  have hex : ∃ X ∈ elementaryAbelianMaxSubgroups C, ¬ X ≤ Q := by
    by_contra! h
    exact hJ (sSup_le h)
  obtain ⟨X, hX, hXQ⟩ := hex
  obtain ⟨B, hB, hBC⟩ := hcompare
  obtain ⟨P₀, hXP₀⟩ := hX.2.1.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
  let e := MulAut.conj g
  have hPP : (P₀ : Subgroup G).map e.toMonoidHom = (P : Subgroup G) := by
    change ((g • P₀ : Sylow 2 G) : Subgroup G) = (P : Subgroup G)
    rw [hg]
  have hAP : X.map e.toMonoidHom ≤ (P : Subgroup G) :=
    (map_mono hXP₀).trans hPP.le
  have hmax : X.map e.toMonoidHom ∈ elementaryAbelianMaxSubgroups (P : Subgroup G) := by
    refine ⟨hAP, hX.2.1.map e.toMonoidHom, fun D hDP hD => ?_⟩
    rw [card_map_of_injective e.injective]
    exact (hB.2.2 D hDP hD).trans (hX.2.2 B hBC hB.2.1)
  refine ⟨X.map e.toMonoidHom, hmax, fun hbot => hXQ ?_⟩
  have hle := (Subgroup.map_eq_bot_iff (X.map e.toMonoidHom)).mp hbot
  rw [QuotientGroup.ker_mk'] at hle
  have hQ : Q.map e.toMonoidHom = Q := Subgroup.Normal.map_conj_eq Q g
  rw [← hQ] at hle
  exact (map_le_map_iff_of_injective e.injective).mp hle

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The doubled fixed-space bound gives an offender and retains the exact nonnegative correction. -/
theorem first_summand_offender (S U A Q : Subgroup G) [IsElementaryAbelian 2 U]
    [Q.Normal] (hU : U ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (f : G →* H) (hker : f.ker = centralizer (U : Set G)) (hkerQ : A ⊓ f.ker ≤ Q)
    (hcore : quotientRank U (U ⊓ centralizer ((A ⊓ Q : Subgroup G) : Set G)) =
      2 * rank ((A ⊓ Q).map f))
    (σ : Representation (ZMod 2) (G ⧸ Q) W)
    (hpair : 2 * fixedCodim σ (A.map (QuotientGroup.mk' Q)) ≤
      quotientRank U (U ⊓ centralizer (A : Set G)))
    (hne : A.map (QuotientGroup.mk' Q) ≠ ⊥) :
    IsOffender σ (A.map (QuotientGroup.mk' Q)) ∧
      2 * fixedCodim σ (A.map (QuotientGroup.mk' Q)) +
        quotientRank (U ⊓ centralizer ((A ⊓ Q : Subgroup G) : Set G))
          (U ⊓ centralizer (A : Set G)) ≤
            2 * rank (A.map (QuotientGroup.mk' Q)) := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have hh := (displayed_rank_inequalities S U A Q hU hA f hker hkerQ hcore).2
  refine ⟨⟨⟨hne, IsElementaryAbelian.map _⟩, ?_⟩, ?_⟩ <;> omega

/-- A genuine FF-star offender exists inside the selected image. This does not yet show
that the entire selected image is best. -/
theorem first_summand_contains_best [FiniteDimensional (ZMod 2) W]
    (S U A Q : Subgroup G) [IsElementaryAbelian 2 U]
    [Q.Normal] (hU : U ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (f : G →* H) (hker : f.ker = centralizer (U : Set G)) (hkerQ : A ⊓ f.ker ≤ Q)
    (hcore : quotientRank U (U ⊓ centralizer ((A ⊓ Q : Subgroup G) : Set G)) =
      2 * rank ((A ⊓ Q).map f))
    (σ : Representation (ZMod 2) (G ⧸ Q) W)
    (hpair : 2 * fixedCodim σ (A.map (QuotientGroup.mk' Q)) ≤
      quotientRank U (U ⊓ centralizer (A : Set G)))
    (hne : A.map (QuotientGroup.mk' Q) ≠ ⊥) :
    ∃ B ≤ A.map (QuotientGroup.mk' Q), IsBestOffender σ B :=
  (first_summand_offender S U A Q hU hA f hker hkerQ hcore σ hpair hne).1.exists_bestOffender σ


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders
