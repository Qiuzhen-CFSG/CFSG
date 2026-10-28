module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Geometry
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity

/-!
# Excluding the normal-L₁ alternative in the HS action

When the tilded center has order two, its unique nonidentity element is fixed
by H. If L₁ were normal in H, the source homogeneous-module construction
would decompose the original tilded U into natural GL₂(2)′-modules. That actor
has no nonzero fixed vector, a contradiction. The second theorem uses the
literal conjugate-center action image, identified with the tilded center by
the source geometry; it does not assume natural L₂(4) coordinates.

This supplies the last contradiction in 14.3.32 once its order-two image and
relative-normality premises have been obtained from the action alternatives.
Construction and exclusion of those alternatives remain with
qt-d-hs-action-source. Centerlessness belongs to qt-d-hs-local-structure;
the earlier naturality and structural premises retain the owners described
in SourceAction.Geometry.

Source: Aschbacher--Smith, 12.8.5(1) and 14.3.32, printed pp.850,1003--1004.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem binary_derived_fixed (v : BinaryLinear.OuterCyclic.Space 2)
    (hv : ∀ a : commutator (BinaryLinear.OuterCyclic.LinearGroup 2), a.val v = v) : v = 0 := by
  by_contra hn
  have hw : (![1, 0] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hw' : (![0, 1] : Fin 2 → ZMod 2) ≠ 0 := by decide
  obtain ⟨a, ha⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero hn hw
  obtain ⟨b, hb⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero hn hw'
  have he := (ha.symm.trans (hv a)).trans ((hv b).symm.trans hb)
  have hf := congrFun he 0
  norm_num at hf

private theorem normal_seed_fixed [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 (F.tilde V)]
    [IsElementaryAbelian 2 (F.tilde F.U)]
    (hLV : L ≤ normalizer (V : Set G)) (A : AmbientNaturalMarking L hLV 3)
    (M : Subgroup G) (hH : F.H ∈ F.Hz L M)
    [((F.Li L 1).subgroupOf F.H).Normal]
    (v : F.tilde (F.UH F.H))
    (hv : ∀ k : F.Li L 1,
      F.localTildeAction F.H le_rfl ⟨k, (F.Li_le L 1 k.property).2⟩ v = v) : v = 1 := by
  let : IsElementaryAbelian 2 (F.tilde (F.UH F.H)) :=
    inferInstanceAs (IsElementaryAbelian 2 (F.tilde F.U))
  obtain ⟨D, r, e, _, he, _⟩ :=
    F.homogeneous_natural_decomposition_of_ambient (by decide) (by decide) L hLV A hH
  have hz : e (Additive.ofMul v) = 0 := by
    funext i
    apply D.coordinates.injective
    change D.coordinates (e (Additive.ofMul v) i) = D.coordinates 0
    rw [map_zero]
    apply binary_derived_fixed
    intro a
    obtain ⟨q, hq⟩ := D.quotientEquiv.surjective a
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) q
    have hh := he k (Additive.ofMul v) i
    change e (Additive.ofMul (F.localTildeAction F.H le_rfl
      ⟨k, (F.Li_le L 1 k.property).2⟩ v)) i = _ at hh
    rw [hv k] at hh
    have hc := congrArg D.coordinates hh
    change D.coordinates (e (Additive.ofMul v) i) =
      D.coordinates (F.localSeedRepresentation L hLV k (e (Additive.ofMul v) i)) at hc
    rw [D.equivariant, hq] at hc
    exact hc.symm
  exact congrArg Additive.toMul (e.injective (hz.trans e.map_zero.symm))

omit [Finite G] in
private theorem fixed_tilded_center [IsMulCommutative V]
    (F : InvariantFlag T V 3) (hcard : Nat.card (F.tilde F.ZU) = 2) :
    ∃ v : F.tilde F.U, v ≠ 1 ∧ ∀ h : F.H, F.localTildeAction F.H le_rfl h v = v := by
  obtain ⟨z, hz, hu⟩ := (Nat.card_eq_two_iff' (1 : F.tilde F.ZU)).mp hcard
  have hZU : F.ZU ≤ F.U := map_subtype_le _
  have htilde : F.tilde F.ZU ≤ F.tilde F.U := map_mono (fun _ hx => hZU hx)
  let v : F.tilde F.U := ⟨z, htilde z.property⟩
  refine ⟨v, ?_, ?_⟩
  · intro he
    apply hz
    apply Subtype.ext
    exact congrArg (fun x : F.tilde F.U => (x : F.G₁tilde)) he
  · intro h
    let a := F.tildeAction F.H F.ZU le_rfl F.H_normalizes_ZU h
    have ha : a z ≠ 1 := fun he => hz (a.injective (he.trans a.map_one.symm))
    have he : a z = z := hu _ ha
    apply Subtype.ext
    exact congrArg (fun x : F.tilde F.ZU => (x : F.G₁tilde)) he

/-- The original L₁ is not normal in H when the tilded center has order two. -/
theorem source_normal_Li_one_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hcard : Nat.card (F.tilde F.ZU) = 2) :
    ¬ ((F.Li L 1).subgroupOf F.H).Normal := by
  intro hn
  let := chosen.elementary
  let := hn
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨htwo, hphi, _⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.tilde_elementary_of_point htwo hphi
  let := F.localKernel_tilde_seed_elementary
  obtain ⟨v, hv, hf⟩ := fixed_tilded_center F hcard
  exact hv (normal_seed_fixed F chosen.normalizes h.naturalMarking _
    (h.point_mem_Hz F alternatives) v (fun k => hf _))

/-- Apply the normal-L₁ exclusion to the actual conjugate-center action image. -/
theorem source_normal_Li_one_exclusion_of_image_order (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hcard : Nat.card (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range = 2) :
    ¬ ((F.Li L 1).subgroupOf F.H).Normal := by
  obtain ⟨e⟩ := source_conjugate_center_image_equiv d earlier hq chosen structural
    alternatives F hne hI g hgP hgH
  exact source_normal_Li_one_exclusion d earlier hq chosen structural alternatives F hne
    ((Nat.card_congr e.toEquiv).symm.trans hcard)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
