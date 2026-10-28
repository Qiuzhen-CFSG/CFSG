module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource.ReducedConsumer
public import Theory.Representation.PSL3Four.SmallTwoGroupAction

/-!
# The original core action excludes the final marked G₂ row

The normal containing component K has characteristic two. Its perfect
conjugation action on its full two-core is therefore nontrivial. Burnside's
Frattini kernel theorem and the binary PSL₃(4) degree-nine bound force
|O₂(K)| ≥ 512. The literal quotient contributes another factor 64, so
32768 divides the order of the actual Sylow intersection T ∩ K.

The previously proved containment T ∩ K ≤ S₀X retains this full kernel.
An actual field-four G₂ diagram would give |S₀X| = 36864, which is not
divisible by 32768. This closes the zero-core branch by a different chief
section from the book: the original K-action on its Frattini section.
It does not assert an unproved identification of V₁ with a model root group.

Source: Aschbacher--Smith 11.1.2, printed p.762; Burnside's Frattini
kernel theorem and GLS III §§2.8.6, 2.8.8, 2.8.10(c), through the proved
PSL₃(4) small-module classification. All actions use the full original core.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension

/-- The full conjugation action on the original core is nontrivial, so its
Frattini action has a nontrivial binary chief section of degree at least nine. -/
private theorem core_card_ge_512 {A : Type*} [Group A] [Finite A] [Nontrivial A]
    [Group.IsPerfect A]
    (hcent : centralizer (pCore 2 A : Set A) ≤ pCore 2 A)
    (hk : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 4) :
    512 ≤ Nat.card (pCore 2 A) := by
  by_contra hsmall
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hk
  have ha := Representation.PSL3Four.action_eq_one_of_card_lt_512 e hF
    (pCore_isPGroup (p := 2) (G := A)) (by omega : Nat.card (pCore 2 A) < 512)
    (MulAut.conjNormal : A →* MulAut (pCore 2 A))
  have hfull : centralizer (pCore 2 A : Set A) = ⊤ := by
    rw [← MulAut.conjNormal_ker_eq_centralizer,ha,MonoidHom.ker_one]
  have hcore : pCore 2 A = ⊤ := top_unique (hfull ▸ hcent)
  have hpa : IsPGroup 2 A := by
    have h := pCore_isPGroup (p := 2) (G := A)
    rw [hcore] at h
    exact h.of_equiv (topEquiv (G := A))
  exact Group.IsPerfect.not_isNilpotent A hpa.isNilpotent

/-- Retain the whole original kernel in the two-part of the original group. -/
private theorem large_core_sylow_divisor {A : Type*} [Group A] [Finite A]
    (hk : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 4)
    (hc : 512 ≤ Nat.card (pCore 2 A)) (P : Sylow 2 A) :
    32768 ∣ Nat.card P := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  have hn9 : 9 ≤ n := by
    by_contra hlt
    have hp : 2^n ≤ 256 := Nat.pow_le_pow_right (by decide) (by omega : n ≤ 8)
    omega
  have hd : 512 ∣ Nat.card (pCore 2 A) := by
    rw [hn]
    exact Nat.pow_dvd_pow 2 hn9
  have hq : 64 ∣ Nat.card (A ⧸ pCore 2 A) := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hk
    rw [Nat.card_congr e.toEquiv]
    have hu := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
    rwa [Matrix.PSL3.LinearThree.card_unipotent,hF] at hu
  have hdA : 2^15 ∣ Nat.card A := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A)]
    exact (show (2:ℕ)^15 = 64*512 by decide) ▸ Nat.mul_dvd_mul hq hd
  exact P.pow_dvd_card_of_pow_dvd_card hdA

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
open CFSG.Quasithin.Chapter12.Section02
variable (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The original containing component has the degree-nine core obstruction;
relative normality is used in its given normalizer, without ambient normality. -/
theorem original_component_core_card_ge_512 {K : Subgroup G}
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    512 ≤ Nat.card (pCore 2 K) := by
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.1.2.subgroupOf_of_le le_rfl hK.1.1
  let : Group.IsPerfect (⊤ : Subgroup K) := htop.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := K)).toMonoidHom) (topEquiv (G := K)).surjective
  have hne : K ≠ ⊥ := by
    intro hk0
    exact hK.1.2.ne_bot (by rw [hk0]; exact bot_subgroupOf _)
  let : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hne
  have hHe : K ∈ Chapter1.He G := Chapter1.lemma_1_1_3_1
    (f.normalizer_mem_He S 0) hne hK.1.1 hK.1.2.subnormal
  exact core_card_ge_512 (Chapter1.mem_He_iff.mp hHe) hk

/-- The original K-Sylow cannot embed in the full G₂(4) Borel. This is the
order consequence of the nontrivial original core action, not an unmarked
model-order comparison. -/
theorem no_original_g2_comparison (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    {K K₀ X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) (b : Bool)
    (e : Iso (originalTriangle T X K₀ (f.Li 1)) (G2Native.amalgam F b)) : False := by
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (f.invariant 0).trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  have hc := original_component_core_card_ge_512 D S f hK hk
  have hd := large_core_sylow_divisor hk hc P
  have hcard : Nat.card P = Nat.card ((T : Subgroup G) ⊓ K : Subgroup G) := by
    rw [hP,←inf_subgroupOf_right (T : Subgroup G) K]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [hcard] at hd
  have he : Nat.card (overlap T X) = 36864 := by
    rw [Nat.card_congr e.middle.toEquiv,Atlas.G2.card_borel,hF]
    decide
  have hi : ((T : Subgroup G) ⊓ K : Subgroup G) ≤ overlap T X :=
    (component_innerSylow_le_commonTwo D S f hu hm hX hK hLK hk).trans le_sup_left
  have hbad : 32768 ∣ 36864 := he ▸ hd.trans (card_dvd_of_le hi)
  norm_num at hbad

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ZeroCoreSource
