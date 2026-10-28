module
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.FourGroupChoice.Replacement

/-!
# Transporting a compatible conjugate reflection

Source: Aschbacher–Smith, printed pp.569–570. The model input is an orbit
identity for outer involutions in the actual `MulAut (alternatingGroup (Fin 6))`,
using the literal inner embedding. Its lift gives a representative `xs` whose
conjugate reflection centralizes the full `N_K(E)`. Faithfulness on `K` and the
supplied action compatibility identify the ambient commutation relation.

The finite orbit identity remains a model obligation. This module does not
claim square stability or the completed source construction.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction
open Subgroup
open CoreReduction
variable {G : Type*} [Group G] [Finite G]

namespace FourGroupChoice

/-- A concrete orbit calculation in `Aut(A₆)`. An outer involution centralizing
its inner Sylow subgroup can be conjugated inside the Sylow subgroup to fix
the full A₆-normalizer of any specified four-group. The inner embedding and
the action on the actual A₆ carrier are part of the statement. -/
@[expose] public def ReflectionOrbit (P : Sylow 2 AutA6) : Prop :=
  ∀ (F : Subgroup A6), IsKleinFour F →
    F.map (MulAut.conj : A6 →* AutA6) ≤ innerSylow P →
    ∀ b ∈ (P : Subgroup AutA6), b ^ 2 = 1 →
      b ∈ centralizer (innerSylow P : Set AutA6) → b ∉ innerSylow P →
      ∃ a ∈ (P : Subgroup AutA6),
        ∀ k ∈ normalizer (F : Set A6), (a⁻¹ * b * a) k = k

omit [Finite G] in
private theorem action_K (d : Setup G) (k : d.K) :
    d.action ⟨k, k_le_h d k.property⟩ = MulAut.conj (d.modelK k) := by
  ext a : 1
  obtain ⟨b, rfl⟩ := d.modelK.surjective a
  apply d.modelK.symm.injective
  apply Subtype.ext
  rw [d.action_compatible]
  simp [MulAut.conj_apply]

/-- The model orbit calculation corrects the reflection by a permissible
change of crossing representative. No square-stability conclusion is used
or claimed here. -/
public theorem exists_replaceX_centralizing (d : Setup G)
    (m : ReflectionOrbit (imageSylow d))
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk)
    {e : G} (he : e ∈ E) (heout : e ∉ zpowers d.zK) :
    ∃ s : d.S, (d.replaceX s).x⁻¹ * e * (d.replaceX s).x ∈
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G) := by
  let F := (E.subgroupOf d.K).map d.modelK.toMonoidHom
  let f : E ≃* F := (subgroupOfEquivOfLe (hE.trans inf_le_right)).symm.trans
    ((E.subgroupOf d.K).equivMapOfInjective d.modelK.toMonoidHom d.modelK.injective)
  have hF : IsKleinFour F :=
    ⟨(Nat.card_congr f.toEquiv).symm.trans IsKleinFour.card_four,
      (Monoid.exponent_eq_of_mulEquiv f).symm.trans IsKleinFour.exponent_two⟩
  have hFD : F.map (MulAut.conj : A6 →* AutA6) ≤ innerSylow (imageSylow d) := by
    rintro _ ⟨a, ⟨k, hk, rfl⟩, rfl⟩
    rw [← skAction_range]
    refine ⟨⟨k, hE hk⟩, ?_⟩
    exact action_K d k
  have he2 : e ^ 2 = 1 := by
    simpa only [pow_two, coe_mul, coe_one] using
      congrArg Subtype.val (IsKleinFour.mul_self (⟨e, he⟩ : E))
  let bS : d.S := ⟨d.x⁻¹ * e * d.x,
    conjugate_le d (hE.trans inf_le_left) (conjugate_mem d he)⟩
  let b := action d bS
  have hbP : b ∈ (imageSylow d : Subgroup AutA6) := by
    rw [imageSylow_eq_range]
    exact ⟨bS, rfl⟩
  have hb2 : b ^ 2 = 1 := by
    have h2 : bS ^ 2 = 1 := by
      apply Subtype.ext
      change (d.x⁻¹ * e * d.x) ^ 2 = 1
      simpa only [map_pow, map_one, MulAut.conj_apply, inv_inv] using
        congrArg (MulAut.conj d.x⁻¹) he2
    change (action d bS) ^ 2 = 1
    rw [← map_pow, h2, map_one]
  have hbC : b ∈ centralizer (innerSylow (imageSylow d) : Set AutA6) := by
    intro a ha
    rw [← skAction_range] at ha
    obtain ⟨k, rfl⟩ := ha
    have hc := d.sk_centralizes_conjugate k.property (bS : G)
      (conjugate_mem d (hE he))
    have hcS : bS * (⟨k, k.property.1⟩ : d.S) = ⟨k, k.property.1⟩ * bS :=
      Subtype.ext hc
    have hh := congrArg (action d) hcS
    change action d (⟨k, k.property.1⟩ : d.S) * action d bS =
      action d bS * action d (⟨k, k.property.1⟩ : d.S)
    simpa only [map_mul] using hh.symm
  have hbout : b ∉ innerSylow (imageSylow d) :=
    conjugate_involution_noninner d (hE he) he2 heout
  obtain ⟨a, ha, hfix⟩ := m F hF hFD b hbP hb2 hbC hbout
  rw [imageSylow_eq_range] at ha
  obtain ⟨s, hs⟩ := ha
  refine ⟨s, ?_⟩
  let cS : d.S := s⁻¹ * bS * s
  have hcval : (cS : G) = (d.replaceX s).x⁻¹ * e * (d.replaceX s).x := by
    change (s : G)⁻¹ * (d.x⁻¹ * e * d.x) * s = (d.x * (s : G))⁻¹ * e * (d.x * s)
    group
  have hcact : action d cS = a⁻¹ * b * a := by
    simp only [cS, map_mul, map_inv, hs]
    rfl
  intro k hk
  let kK : d.K := ⟨k, hk.1⟩
  have hkN : kK ∈ normalizer (E.subgroupOf d.K : Set d.K) := by
    apply mem_normalizer_iff.mpr
    intro u
    change (u : G) ∈ E ↔ k * (u : G) * k⁻¹ ∈ E
    exact mem_normalizer_iff.mp hk.2 u
  have hkF : d.modelK kK ∈ normalizer (F : Set A6) :=
    (le_normalizer_map d.modelK.toMonoidHom)
      (mem_map_of_mem d.modelK.toMonoidHom hkN)
  have hfixed : action d cS (d.modelK kK) = d.modelK kK := by
    rw [hcact]
    exact hfix _ hkF
  have hh := d.action_compatible (⟨cS, s_le_h d cS.property⟩ : d.H) kK
  change (d.modelK.symm (action d cS (d.modelK kK)) : G) =
    (cS : G) * k * (cS : G)⁻¹ at hh
  rw [hfixed, d.modelK.symm_apply_apply] at hh
  change k = (cS : G) * k * (cS : G)⁻¹ at hh
  rw [← hcval]
  calc
    k * (cS : G) = ((cS : G) * k * (cS : G)⁻¹) * cS := by rw [← hh]
    _ = (cS : G) * k := by group

end FourGroupChoice
end CFSG.Quasithin.Chapter2.A6ShadowConstruction
