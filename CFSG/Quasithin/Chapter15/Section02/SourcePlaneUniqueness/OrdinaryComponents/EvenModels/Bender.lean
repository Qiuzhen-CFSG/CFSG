module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.Borel
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import Theory.SpecificGroups.PSL2.OrdinaryBorelGeometry
public import Theory.SpecificGroups.Suzuki.BorelResidualRigidity
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Unitary.Model

/-!
# Exclusion of the ordinary Bender rows

In each actual PSL₂, PSU₃ or Suzuki model, a proper overgroup of a full
Sylow two-subgroup normalizes that Sylow. Apply this to the marked fixed
subgroup. The maximal-intersection core argument then makes the marked
involution fix the entire Borel. The concrete Borel fixer theorems force
it to be trivial, contradicting its original order two.

Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 Candidates.ComponentStructure ClassificationModels
open ChapterF.Source

private theorem proper_sylow_overgroup_transport
    {D E : Type*} [Group D] [Group E] [Finite D] [Finite E]
    (e : D ≃* E) (hfacts : ∀ S : Sylow 2 E, RankOneSylowFacts S)
    (Q : Sylow 2 D) (B : Subgroup D) (hQB : (Q : Subgroup D) ≤ B) (hB : B ≠ ⊤) :
    B ≤ normalizer (Q : Set D) := by
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hb : B.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hB
    have hh := congrArg (comap e.toMonoidHom) he
    simpa only [comap_map_eq,e.toMonoidHom.ker_eq_bot e.injective,sup_bot_eq,comap_top] using hh
  have hh := (hfacts R).unique_maximal (B.map e.toMonoidHom)
    (map_mono hQB) (lt_top_iff_ne_top.mpr hb)
  change B.map e.toMonoidHom ≤ normalizer ((Q : Subgroup D).map e.toMonoidHom : Set E) at hh
  rw [← map_equiv_normalizer_eq] at hh
  exact (map_le_map_iff_of_injective e.injective).mp hh

/-- Every proper full-Sylow overgroup in a Bender model normalizes that Sylow. -/
theorem bender_proper_sylow_overgroup_normalizes
    {D : Type*} [Group D] [Finite D] (hm : IsBenderModel D)
    (Q : Sylow 2 D) (B : Subgroup D) (hQB : (Q : Subgroup D) ≤ B) (hB : B ≠ ⊤) :
    B ≤ normalizer (Q : Set D) := by
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact proper_sylow_overgroup_transport e
      (Linear.projective_facts F n (by omega) hF) Q B hQB hB
  | unitary n hn hm =>
    obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    exact proper_sylow_overgroup_transport e
      (rankOneSylowFacts_psu3 J n (by omega) hF hc) Q B hQB hB
  | suzuki m hm he =>
    obtain ⟨e⟩ := he
    exact proper_sylow_overgroup_transport e (suzuki_rankOneSylowFacts m) Q B hQB hB

private theorem fixer_transport
    {D E : Type*} [Group D] [Group E] [Finite D] [Finite E]
    (e : D ≃* E)
    (hfixer : ∀ (Q : Sylow 2 E) (a : MulAut E), a^2=1 →
      (∀ x ∈ normalizer (Q : Set E), a x=x) → a=1)
    (Q : Sylow 2 D) (a : MulAut D) (ha : a^2=1)
    (hfix : ∀ x ∈ normalizer (Q : Set D), a x=x) : a=1 := by
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hh : MulAut.congr e a = 1 := by
    apply hfixer R
    · rw [← map_pow,ha,map_one]
    · intro x hx
      have hx' : x ∈ (normalizer (Q : Set D)).map e.toMonoidHom := by
        have hB : (normalizer (Q : Set D)).map e.toMonoidHom = normalizer (R : Set E) :=
          map_equiv_normalizer_eq (Q : Subgroup D) e
        exact hB.symm ▸ hx
      obtain ⟨y,hy,rfl⟩ := hx'
      change e (a (e.symm (e y))) = e y
      rw [e.symm_apply_apply,hfix y hy]
  exact (MulAut.congr e).injective (hh.trans (map_one _).symm)

/-- The concrete Bender Borels have trivial involutory pointwise fixer. -/
theorem bender_borel_fixer
    {D : Type*} [Group D] [Finite D] [IsSimpleGroup D] (hm : IsBenderModel D)
    (Q : Sylow 2 D) (a : MulAut D) (ha : a^2=1)
    (hfix : ∀ x ∈ normalizer (Q : Set D), a x=x) : a=1 := by
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
    apply fixer_transport e (fun R b _ hb => ?_) Q a ha hfix
    apply Theory.PSL2.OrdinaryBorel.normalizer_fixer hF _ R b hb
    rw [hF]
    exact lt_of_eq_of_lt (by decide : 2=2^1) (Nat.pow_lt_pow_right (by decide) hn)
  | unitary n hn hm =>
    exact RankOne.DiagonalExclusion.UnitaryModel.borel_fixer_eq_one hn hm Q a ha hfix
  | suzuki m hm he =>
    exact BenderSuzuki.MatrixGroups.suzuki_aut_eq_one_of_fixing_borel (by omega) he.some Q a hfix

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include d

/-- All three Bender rows are impossible on the original minimal escaping component. -/
theorem not_bender_component
    (hI : MinimalPlaneEscape Mc ZS I)
    (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hs : IsSimpleGroup c.component) (hm : IsBenderModel c.component)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  let := hs
  have hai := marked_component_twoCentral d c hI.1 hP hz hzne a ha hi
  obtain ⟨_,ho,Q,hQ⟩ := hai
  have hQfix : (Q : Subgroup c.component) ≤ a.fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hQ ⟨x,hx⟩)
  have hproper : a.fixedSubgroup ≠ ⊤ := by
    intro he
    have ha1 : a=1 := by
      apply MulEquiv.ext
      intro x
      exact (MulAut.mem_fixedSubgroup _ _).mp (he ▸ mem_top x)
    rw [ha1,orderOf_one] at ho
    omega
  have hn := bender_proper_sylow_overgroup_normalizes hm Q a.fixedSubgroup hQfix hproper
  have hfix := marked_component_borel_fixed d c hI hz hzne a ha ⟨hi,ho,Q,hQ⟩ Q hQfix hn
  have ha1 := bender_borel_fixer hm Q a (ho ▸ pow_orderOf_eq_one a) hfix
  rw [ha1,orderOf_one] at ho
  omega
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
