module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalExtraspecialSource
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.PolarCoinvariants
public import Theory.Representation.FrattiniCoinvariantCommutator

/-!
# The original normal closure lies in the selected component

The actual extraspecial closure has nondegenerate Frattini polar. Its odd
projective orbit therefore has full component displacement, and Frattini
lifting gives U=[U,K]. In particular U lies in the original marked K,
retaining the same ambient inclusions used by the F.1.1 amalgam.

Source: Aschbacher–Smith 14.2.16 and F.1.12, printed pp.985–986 and 262–264.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter12.Section08
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_normal_bender_closure_commutator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (n : ℕ) (hm : BenderModel ((H ⊓ M).subgroupOf H) K n) :
    let U := conjugateSpanBy (localModule T M) H
    U = ⁅U,K.map H.subtype⁆ ∧ U ≤ K.map H.subtype := by
  classical
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h,hphi,hphic,w,hw,hfix,hspan,hzero,hpolar⟩ :=
    source_frattini_seed_orbit hG T hempty hM hu hmany hcard e H hH.1 hne
  obtain ⟨hc,_⟩ := source_normal_bender_closure_extraspecial_orders
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen n hm
  obtain ⟨hr,F,hfield,hfinite,hchar,hF,hmodel⟩ :=
    source_normal_bender_nonabelian_models hG T hempty hM hu hmany hcard e
      H hH hnH hne K hK hqK hgen n hm
  let := hfield
  let := hfinite
  let := hchar
  let := SmallFrattini.quotientElementary h.U_isPGroup
  let ρ := frattiniRepresentation D h.U_isPGroup
  let B := SmallFrattini.quotientBilinearForm h.U_isPGroup hphic
  have hker : B.ker = ⊥ := by
    have hc' := SmallFrattini.center_card_eq_two_pow_polar_radical h.U_isPGroup hphic
    change Nat.card (center D.U) = 2 ^ (Module.finrank (ZMod 2) B.ker + 1) at hc'
    change Nat.card (center D.U) = 2 at hc
    rw [hc] at hc'
    have hd := Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
      ((pow_one 2).trans hc')
    apply Submodule.finrank_eq_zero.mp
    omega
  have hMN : M ≤ normalizer (D.V : Set G) :=
    (InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1).le
  have hfixed (g : H) (hg : g ∈ (H ⊓ M).subgroupOf H) :
      ρ g (Additive.ofMul w) = Additive.ofMul w := by
    change Additive.ofMul (frattiniActor D g w) = Additive.ofMul w
    exact congrArg Additive.ofMul (hfix g (hMN hg.2))
  have hSM : (T.subtype hH.1.1.2 : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
    intro t ht
    exact ⟨t.property,hM.1.2 ht⟩
  have hn : 0 < n := by rcases hr with rfl | rfl <;> decide
  have hodd : Odd (Nat.card (BenderSuzuki.Converse.P1 F)) := by
    rw [Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp),hF]
    exact (Nat.even_pow.mpr ⟨even_two,by omega⟩).add_odd odd_one
  have hcoins := hmodel.orbit_polar_coinvariants _ K _ hgen hSM
    (BenderSuzuki.Converse.pInf F) (BenderSuzuki.Converse.psl2_two_pretransitive (F := F))
    ρ (Additive.ofMul w) hfixed hspan B
    (SmallFrattini.quotientBilinearForm_isAlt _ _) hpolar
    (fun g x y => SmallFrattini.quotientBilinearForm_invariant
      h.U_isPGroup hphic (closureActor D g) x.toMul y.toMul) hker hodd
  let a : K →* G := H.subtype.comp K.subtype
  have har : a.range = K.map H.subtype := by
    rw [MonoidHom.range_comp,range_subtype]
  have han : a.range ≤ normalizer (D.U : Set G) := by
    rw [har]
    exact (map_subtype_le K).trans (le_normalizer_conjugateSpanBy _ _)
  let q := QuotientGroup.mk' (frattini D.U)
  let f : D.U →* Multiplicative (Additive (D.U ⧸ frattini D.U)) := {
    toFun u := Multiplicative.ofAdd (Additive.ofMul (q u))
    map_one' := congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) (map_one q)
    map_mul' := fun x y => congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) (map_mul q x y) }
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (frattini D.U) v.toAdd.toMul
    exact ⟨u,congrArg (fun x => Multiplicative.ofAdd (Additive.ofMul x)) hu⟩
  have hfk : f.ker ≤ frattini D.U := by
    intro u hu
    exact (QuotientGroup.eq_one_iff u).mp hu
  have hact (k : K) (u u' : D.U) (he : (u' : G) = a k * (u : G) * (a k)⁻¹) :
      (f u').toAdd = (ρ.comp K.subtype) k (f u).toAdd := by
    have hue : u' = closureActor D k.val u :=
      Subtype.ext (he.trans (closureActor_apply D k.val u).symm)
    change Additive.ofMul (q u') = Additive.ofMul (frattiniActor D k.val (q u))
    rw [hue]
    exact congrArg Additive.ofMul (quotientAut_apply_mk (frattini D.U)
      (closureActor D k.val) u).symm
  have hcomm := Representation.subgroup_eq_commutator_of_frattini_coinvariants
    D.U a han (ρ.comp K.subtype) f hf hfk hact hcoins
  rw [har] at hcomm
  refine ⟨hcomm,?_⟩
  change D.U ≤ K.map H.subtype
  rw [hcomm]
  apply le_normalizer_iff_commutator_le_right.mp
  have hHN : H ≤ normalizer (K.map H.subtype : Set G) := by
    have hh := K.le_normalizer_map H.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  exact h.U_le_H.trans hHN
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
