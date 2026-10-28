module

public import Theory.SpecificGroups.G2.CoverFixedNaturalSections.CentralCover
public import Theory.SpecificGroups.G2.CoverFixedNaturalSections.Residual

/-!
# Excluding natural sections in fixed residuals of G₂(4) covers

The fixed residual of a Sylow-fixing inner involution in a perfect central
two-cover maps onto the actual highest-root centralizer. Its normalized
abelian two-core subgroups are central, by the root-coordinate calculation
and centralizer lifting. Consequently none has a binary natural SL₂(4)
section. The proof transports the residual to any supplied injective
ambient image and keeps the original conjugation and actor map.

This proves more than the quasisimple nontrivial-center case: perfectness
suffices, and only surjectivity of the supplied SL₂(4) map is needed. In
particular it applies to the prescribed map with kernel exactly the
two-core, without replacing that map or classifying the covering kernel.

Source: Aschbacher–Smith 14.7.68(2), printed p.1071 (PDF p.1088),
1.1.5(3)(b), pp.501–503, and F.1.11–12, pp.262–264.
-/

public section

open Subgroup
namespace Atlas.G2.CoverFixedNaturalSections

theorem not_naturalSection {A D F : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    [Group D] [Finite D] [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : (A ⧸ pCore 2 A) ≃* Model F)
    (hZ : center A = pCore 2 A) (α : MulAut A)
    (hne : α ≠ 1) (hsq : α ^ 2 = 1) (hi : α ∈ (MulAut.conj (G := A)).range)
    (P : Sylow 2 A) (hP : ∀ x ∈ P, α x = x)
    (i : A →* D) (hinj : Function.Injective i)
    (B E : Subgroup D) [IsElementaryAbelian 2 B]
    (hB : B ≤ ((MulAut.embeddedFixedResidual 2 α).map i).pCoreIn 2)
    (q : (MulAut.embeddedFixedResidual 2 α).map i →* Representation.SL2FourNatural.SL)
    (hq : Function.Surjective q) :
    ¬ Nonempty (Representation.BinaryConjugationSection
      ((MulAut.embeddedFixedResidual 2 α).map i) B E
      (Representation.SL2FourNatural.naturalRepresentation.comp q)) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 2) (by
    norm_num only [← Nat.card_eq_fintype_card, hF])
  have hsize : 2 < Nat.card F := by omega
  obtain ⟨f,hf,hc,hk⟩ := exists_fixedResidual_local_cover hsize e hZ α hne hsq hi P hP
  let R₀ := MulAut.embeddedFixedResidual 2 α
  let R := R₀.map i
  let ei : R₀ ≃* R := R₀.equivMapOfInjective i hinj
  let f' : R →* LieParabolicSetup.local₁ (F := F) := f.comp ei.symm.toMonoidHom
  have hf' : Function.Surjective f' := hf.comp ei.symm.surjective
  have hc' : f'.ker ≤ center R := by
    intro x hx
    have hx' : ei.symm x ∈ f.ker := hx
    rw [mem_center_iff]
    intro y
    apply ei.symm.injective
    simpa only [map_mul] using mem_center_iff.mp (hc hx') (ei.symm y)
  have hk' : IsPGroup 2 f'.ker := by
    change IsPGroup 2 (f.comp ei.symm.toMonoidHom).ker
    change IsPGroup 2 (f.ker.comap ei.symm.toMonoidHom)
    exact hk.comap_of_injective ei.symm.toMonoidHom ei.symm.injective
  have hp : IsPPerfect 2 R :=
    (isPPerfect_embedded_pResidual 2 α.fixedSubgroup).of_surjective ei.toMonoidHom ei.surjective
  exact not_naturalSection_of_cover hsize R B E hp f' hf' hc' hk' hB q hq
end Atlas.G2.CoverFixedNaturalSections
