module

public import Theory.Representation.SL2FourNaturalSylowFixed
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover

/-!
# Fixed lines in the original sections of §14.7

The natural S₅ point stabilizers are Sylow subgroups. A stable subspace
of the original module which injects into the natural quotient has exactly
the quotient's fixed vectors in its image. Applying this to the two
complements in 14.7.65 and 14.7.70 gives their common fixed line.

The main transport uses the original actor and the same quotient map p;
it does not require that the whole covering module be an S₅-module. The
action on ker p remains arbitrary. A separate application records the
complement supplied by ModuleCover when its S₅-action hypothesis is present.
The point-centralizer application retains the actual subgroup coordinates
and the kernel of the original H → S₅ quotient.

Source: Aschbacher–Smith, 14.7.65, 14.7.67 and 14.7.70,
printed pp.1070 and 1073–1074. The ambient fusion and rank bounds remain
with the critical-fusion and local-structure source owners.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure
open Subgroup Representation Representation.OneCohomology
open Representation.SL2FourNatural

/-- The original natural action's nonzero-vector stabilizer is an actual Sylow. -/
def naturalPointSylow (a : ChapterJ.L2FourAction) (v : V) (hv : v ≠ 0) :
    Sylow 2 ChapterJ.S5 :=
  SL2FourNaturalSylowFixed.pointSylow a.action a.marking a.restriction v hv

theorem naturalPointSylow_coe (a : ChapterJ.L2FourAction) (v : V) (hv : v ≠ 0) :
    (naturalPointSylow a v hv : Subgroup ChapterJ.S5) =
      SL2FourNaturalSylowFixed.vectorStabilizer a.action v := rfl

/-- No choice of Frobenius coordinates is needed for the natural fixed line. -/
theorem natural_sylow_fixed_finrank (a : ChapterJ.L2FourAction)
    (P : Sylow 2 ChapterJ.S5) :
    Module.finrank (ZMod 2) (Representation.invariants (a.action.comp (P : Subgroup ChapterJ.S5).subtype)) = 1 :=
  SL2FourNaturalSylowFixed.fixed_finrank a.action a.marking a.restriction P

section OriginalActor
variable {Γ W : Type*} [Group Γ] [AddCommGroup W] [Module (ZMod 2) W]
  (a : ChapterJ.L2FourAction) (ρ : Representation (ZMod 2) Γ W)
  (q : Γ →* ChapterJ.S5) (p : ρ.IntertwiningMap (a.action.comp q))
  (T : Subgroup Γ) (P : Sylow 2 ChapterJ.S5)
  (hTP : T.map q = (P : Subgroup ChapterJ.S5))

private theorem projection_action (g : Γ) (w : W) :
    p (ρ g w) = a.action (q g) (p w) :=
  LinearMap.congr_fun (p.isIntertwining' g) w

/-- The same p identifies fixed vectors in every stable subspace on which
it is injective. In particular the quotient kernel need not fix all of W. -/
def fixedSubspaceEquiv (A : Submodule (ZMod 2) W)
    (hA : ∀ t : T, ∀ x ∈ A, ρ t x ∈ A)
    (hd : Disjoint A p.toLinearMap.ker) :
    ↥(A ⊓ (Representation.invariants (ρ.comp T.subtype))) ≃ₗ[ZMod 2]
      ↥((A.map p.toLinearMap) ⊓
        (Representation.invariants (a.action.comp (P : Subgroup ChapterJ.S5).subtype))) := by
  let f : ↥(A ⊓ (Representation.invariants (ρ.comp T.subtype))) →ₗ[ZMod 2]
      ↥((A.map p.toLinearMap) ⊓
        (Representation.invariants (a.action.comp (P : Subgroup ChapterJ.S5).subtype))) := {
    toFun x := ⟨p x, ⟨⟨x, x.property.1, rfl⟩, by
      intro g
      have hg : g.val ∈ T.map q := hTP.symm ▸ g.property
      obtain ⟨t, ht, htg⟩ := hg
      change a.action g.val (p x) = p x
      rw [← htg, ← projection_action a ρ q p]
      exact congrArg p (x.property.2 ⟨t, ht⟩)⟩⟩
    map_add' x y := Subtype.ext (p.map_add x y)
    map_smul' c x := Subtype.ext (p.map_smul c x) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply (Submodule.disjoint_def.mp hd)
    · exact A.sub_mem x.property.1 y.property.1
    · change p (x.val - y.val) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
  · intro y
    obtain ⟨x, hx, hxy⟩ := y.property.1
    have hfix : ∀ t : T, ρ t x = x := by
      intro t
      apply sub_eq_zero.mp
      apply (Submodule.disjoint_def.mp hd)
      · exact A.sub_mem (hA t x hx) hx
      · change p (ρ t x - x) = 0
        have hpact : p (ρ t x) = a.action (q t) (p x) :=
          LinearMap.congr_fun (p.isIntertwining' t) x
        have hpx : p x = y := hxy
        rw [map_sub, hpact, hpx]
        have htP : q t ∈ P := by
          change q t ∈ (P : Subgroup ChapterJ.S5)
          rw [← hTP]
          exact mem_map_of_mem q t.property
        exact sub_eq_zero.mpr
          (y.property.2 ⟨q t, htP⟩)
    exact ⟨⟨x, hx, hfix⟩, Subtype.ext hxy⟩

theorem fixedSubspaceEquiv_apply (A : Submodule (ZMod 2) W)
    (hA : ∀ t : T, ∀ x ∈ A, ρ t x ∈ A)
    (hd : Disjoint A p.toLinearMap.ker)
    (x : ↥(A ⊓ (Representation.invariants (ρ.comp T.subtype)))) :
    (fixedSubspaceEquiv a ρ q p T P hTP A hA hd x : V) = p x := rfl

include hTP in
/-- A marked complement of the natural upper line has one T-fixed dimension.
This applies to both V-tilde and the original displacement F-tilde. -/
theorem original_complement_fixed_finrank
    (hupper : ∀ t : F, alternatingActor a (upper t) ∈ P)
    (A : Submodule (ZMod 2) W)
    (hA : ∀ t : T, ∀ x ∈ A, ρ t x ∈ A)
    (hd : Disjoint A p.toLinearMap.ker)
    (himage : A.map p.toLinearMap = SL2FourNatural.upperFixed) :
    Module.finrank (ZMod 2) ↥(A ⊓ (Representation.invariants (ρ.comp T.subtype))) = 1 := by
  have hfix : (Representation.invariants (a.action.comp (P : Subgroup ChapterJ.S5).subtype)) ≤
      SL2FourNatural.upperFixed := by
    intro v hv
    apply (SL2FourNatural.mem_upperFixed v).mpr
    apply (SL2FourNatural.upper_fixed_iff v).mp
    intro t
    exact (a.restriction (upper t) v).symm.trans
      (hv ⟨alternatingActor a (upper t), hupper t⟩)
  have hdims := (fixedSubspaceEquiv a ρ q p T P hTP A hA hd).finrank_eq
  rw [himage, inf_eq_right.mpr hfix, natural_sylow_fixed_finrank] at hdims
  exact hdims

/-- The source's fixed-space decomposition retains the original action on
the K-fixed kernel. The hypothesis on R is precisely the earlier 14.7.65
decomposition, not a later fixed-space conclusion. -/
theorem original_fixed_decomposition
    (R : Subgroup Γ) (hRT : R ≤ T) (A : Submodule (ZMod 2) W)
    (hA : ∀ t : T, ∀ x ∈ A, ρ t x ∈ A)
    (hd : Disjoint A p.toLinearMap.ker)
    (h65 : (Representation.invariants (ρ.comp R.subtype)) = A ⊔ p.toLinearMap.ker) :
    (Representation.invariants (ρ.comp T.subtype)) =
      (A ⊓ (Representation.invariants (ρ.comp T.subtype))) ⊔
      (p.toLinearMap.ker ⊓ (Representation.invariants (ρ.comp T.subtype))) := by
  apply le_antisymm
  · intro w hw
    have hwR : w ∈ (Representation.invariants (ρ.comp R.subtype)) :=
      fun r => hw ⟨r, hRT r.property⟩
    rw [h65] at hwR
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hwR
    have hyfix (t : T) : ρ t y ∈ p.toLinearMap.ker := by
      change p (ρ t y) = 0
      rw [projection_action a ρ q p, show p y = 0 from hy, map_zero]
    have hxfix : ∀ t : T, ρ t x = x := by
      intro t
      apply sub_eq_zero.mp
      apply (Submodule.disjoint_def.mp hd)
      · exact A.sub_mem (hA t x hx) hx
      · have hs : ρ t x + ρ t y = x + y := by
          rw [← map_add, hxy]
          exact hw t
        have he : ρ t x - x = y - ρ t y := by
          calc
            ρ t x - x = (ρ t x + ρ t y) - (x + ρ t y) := by abel
            _ = (x + y) - (x + ρ t y) := by rw [hs]
            _ = y - ρ t y := by abel
        rw [he]
        exact p.toLinearMap.ker.sub_mem hy (hyfix t)
    have hyfixed : ∀ t : T, ρ t y = y := by
      intro t
      have hs : ρ t x + ρ t y = x + y := by
        rw [← map_add, hxy]
        exact hw t
      rw [hxfix t] at hs
      exact add_left_cancel hs
    exact Submodule.mem_sup.mpr ⟨x, ⟨hx, hxfix⟩, y, ⟨hy, hyfixed⟩, hxy⟩
  · exact sup_le inf_le_right inf_le_right

end OriginalActor

section CoverApplication
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) ChapterJ.S5 W}

/-- The literal p-image of any complement from 14.7.65 is the natural upper
line. This is a specialization to the existing ModuleCover hypotheses. -/
theorem upper_complement_image (a : ChapterJ.L2FourAction)
    (p : σ.IntertwiningMap a.action) (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (A : Submodule (ZMod 2) W)
    (h65 : SL2CentralExtension.upperFixed (σ.comp (alternatingActor a)) =
      A ⊔ p.toLinearMap.ker) : A.map p.toLinearMap = SL2FourNatural.upperFixed := by
  have himage : (SL2CentralExtension.upperFixed (σ.comp (alternatingActor a))).map
      p.toLinearMap = SL2FourNatural.upperFixed := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      apply (SL2FourNatural.mem_upperFixed _).mpr
      exact (SL2CentralExtension.mem_upperFixed_iff _ p.toLinearMap hp
        (fun g w => (LinearMap.congr_fun (p.isIntertwining' (alternatingActor a g)) w).trans
          (a.restriction g (p w)))
        (fun w hw g => hk hw g) w).mp hw
    · intro hv
      obtain ⟨w, rfl⟩ := hp v
      refine ⟨w, ?_, rfl⟩
      apply (SL2CentralExtension.mem_upperFixed_iff _ p.toLinearMap hp
        (fun g w => (LinearMap.congr_fun (p.isIntertwining' (alternatingActor a g)) w).trans
          (a.restriction g (p w)))
        (fun w hw g => hk hw g) w).mpr
      exact (SL2FourNatural.mem_upperFixed _).mp hv
  have hpk : p.toLinearMap.ker.map p.toLinearMap = ⊥ :=
    LinearMap.le_ker_iff_map.mp le_rfl
  rw [h65, Submodule.map_sup, hpk, sup_bot_eq] at himage
  exact himage

/-- The actual displacement in ModuleCover maps onto that same upper line;
its injectivity is proved, not requested as a new source premise. -/
theorem upper_displacement_image (a : ChapterJ.L2FourAction)
    (p : σ.IntertwiningMap a.action) (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (hi : ∀ A B : Submodule (ZMod 2) W,
      (∀ g v, v ∈ A → σ (alternatingActor a g) v ∈ A) →
      (∀ g v, v ∈ B → σ (alternatingActor a g) v ∈ B) →
      IsCompl A B → A = ⊥ ∨ B = ⊥)
    (t : F) (ht : t ≠ 0) :
    Disjoint (σ (alternatingActor a (upper t)) - LinearMap.id).range p.toLinearMap.ker ∧
      ((σ (alternatingActor a (upper t)) - LinearMap.id).range).map p.toLinearMap =
        SL2FourNatural.upperFixed := by
  obtain ⟨hd, hc⟩ := original_section_upper_complement a p hp hk hi t ht
  exact ⟨hd, upper_complement_image a p hp hk _ hc⟩

/-- The literal ModuleCover displacement has one Sylow-fixed dimension
after its upper actor has been placed in the Sylow center, as in 14.7.70.
Only this specialization uses ModuleCover's existing S₅-action hypothesis. -/
theorem upper_displacement_fixed_finrank (a : ChapterJ.L2FourAction)
    (p : σ.IntertwiningMap a.action) (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed (σ.comp (alternatingActor a)))
    (hi : ∀ A B : Submodule (ZMod 2) W,
      (∀ g v, v ∈ A → σ (alternatingActor a g) v ∈ A) →
      (∀ g v, v ∈ B → σ (alternatingActor a g) v ∈ B) →
      IsCompl A B → A = ⊥ ∨ B = ⊥)
    (P : Sylow 2 ChapterJ.S5)
    (hupper : ∀ s : F, alternatingActor a (upper s) ∈ P)
    (t : F) (ht : t ≠ 0)
    (hcentral : ∀ g : P, (g : ChapterJ.S5) * alternatingActor a (upper t) =
      alternatingActor a (upper t) * g) :
    Module.finrank (ZMod 2)
      ↥((σ (alternatingActor a (upper t)) - LinearMap.id).range ⊓
        (Representation.invariants (σ.comp (P : Subgroup ChapterJ.S5).subtype))) = 1 := by
  obtain ⟨hd, him⟩ := upper_displacement_image a p hp hk hi t ht
  apply original_complement_fixed_finrank a σ (MonoidHom.id _) p
    (P : Subgroup ChapterJ.S5) P (by simp) hupper _ _ hd him
  intro g w hw
  obtain ⟨x, rfl⟩ := hw
  refine ⟨σ g x, ?_⟩
  change σ (alternatingActor a (upper t)) (σ g x) - σ g x =
    σ g (σ (alternatingActor a (upper t)) x - x)
  rw [map_sub]
  congr 1
  calc
    _ = σ (alternatingActor a (upper t) * g) x := by rw [map_mul]; rfl
    _ = σ (g * alternatingActor a (upper t)) x := by rw [hcentral g]
    _ = _ := by rw [map_mul]; rfl

end CoverApplication

section PointCentralizer
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H U V₁ V₂ : Subgroup G}

/-- The actual order-four flag plane has an order-two image in U/V₁.
Consequently each actor normalizing that plane fixes its image pointwise. -/
theorem flag_plane_fixed [Finite G]
    (ρ : Representation (ZMod 2) H W)
    (d : BinaryConjugationSection H U V₁ ρ)
    (hV₂U : V₂ ≤ U) (hV₁V₂ : V₁ ≤ V₂)
    (hV₁ : Nat.card V₁ = 2) (hV₂ : Nat.card V₂ = 4)
    (t : H) (ht : (t : G) ∈ normalizer (V₂ : Set G))
    (v : U) (hv : (v : G) ∈ V₂) :
    ρ t (d.coordinates v).toAdd = (d.coordinates v).toAdd := by
  let r : V₂ →* Multiplicative W := d.coordinates.comp (inclusion hV₂U)
  have hk : r.ker = V₁.subgroupOf V₂ := by
    ext x
    exact d.coordinates_eq_one_iff (inclusion hV₂U x)
  have hr : Nat.card r.range = 2 := by
    have hc := card_eq_card_quotient_mul_card_subgroup r.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv, hk,
      Nat.card_congr (subgroupOfEquivOfLe hV₁V₂).toEquiv, hV₁, hV₂] at hc
    omega
  let x : V₂ := ⟨v, hv⟩
  let y : V₂ := ⟨t * v * (t : G)⁻¹, (mem_normalizer_iff.mp ht v).mp hv⟩
  have hy : (r y).toAdd = ρ t (d.coordinates v).toAdd := d.equivariant t v
  by_cases hx : r x = 1
  · have hx' : (d.coordinates v).toAdd = 0 := hx
    rw [hx', map_zero]
  · have hy' : r y ≠ 1 := by
      intro hz
      apply hx
      have hz' : ρ t (d.coordinates v).toAdd = 0 := hy.symm.trans hz
      apply Multiplicative.toAdd.injective
      change (d.coordinates v).toAdd = 0
      simpa only [ρ.inv_self_apply, map_zero] using congrArg (ρ t⁻¹) hz'
    obtain ⟨z, _, hu⟩ := (Nat.card_eq_two_iff' (1 : r.range)).mp hr
    have he : (⟨r y, ⟨y, rfl⟩⟩ : r.range) = ⟨r x, ⟨x, rfl⟩⟩ :=
      (hu _ (fun h => hy' (congrArg Subtype.val h))).trans
        (hu _ (fun h => hx (congrArg Subtype.val h))).symm
    exact hy.symm.trans (congrArg (fun z : r.range => z.val.toAdd) he)

/-- The source 14.7.67 point-centralizer implication on the original
subgroups. The nonzero fixed point is the preceding V₂/V₁ flag marking.
The actual quotient kernel is retained and its containment in T is used. -/
theorem source_point_centralizer_le
    (a : ChapterJ.L2FourAction) (ρ : Representation (ZMod 2) H W)
    (qH : H →* ChapterJ.S5)
    (d : BinaryConjugationSection H U V₁ ρ)
    (p : ρ.IntertwiningMap (a.action.comp qH))
    (T : Subgroup H) (P : Sylow 2 ChapterJ.S5)
    (hTP : T.map qH = (P : Subgroup ChapterJ.S5))
    (hker : qH.ker = (H.pCoreIn 2).subgroupOf H)
    (hQT : (H.pCoreIn 2).subgroupOf H ≤ T)
    (v : U) (hv₂ : (v : G) ∈ V₂)
    (hv : p (d.coordinates v).toAdd ≠ 0)
    (hTv : ∀ t : T, ρ t (d.coordinates v).toAdd = (d.coordinates v).toAdd) :
    H ⊓ centralizer (V₂ : Set G) ≤ T.map H.subtype := by
  have hfix : ∀ g : P, a.action g (p (d.coordinates v).toAdd) =
      p (d.coordinates v).toAdd := by
    intro g
    have hg : g.val ∈ T.map qH := hTP.symm ▸ g.property
    obtain ⟨t, ht, htg⟩ := hg
    rw [← htg, ← projection_action a ρ qH p, hTv ⟨t, ht⟩]
  have hstab := SL2FourNaturalSylowFixed.vectorStabilizer_eq_of_fixed
    a.action a.marking a.restriction P _ hv hfix
  intro x hx
  let h : H := ⟨x, hx.1⟩
  have hconj : (h : G) * (v : G) * (h : G)⁻¹ = v := by
    have hc := (mem_centralizer_iff.mp hx.2) v hv₂
    calc
      _ = (v : G) * (h : G) * (h : G)⁻¹ := by rw [hc]
      _ = v := by group
  have hcoord : ρ h (d.coordinates v).toAdd = (d.coordinates v).toAdd := by
    rw [← d.equivariant]
    exact congrArg (fun u : U => (d.coordinates u).toAdd) (Subtype.ext hconj)
  have him : qH h ∈ P := by
    change qH h ∈ (P : Subgroup ChapterJ.S5)
    rw [← hstab]
    change a.action (qH h) (p (d.coordinates v).toAdd) = p (d.coordinates v).toAdd
    rw [← projection_action a ρ qH p, hcoord]
  have him' : qH h ∈ T.map qH := hTP.symm ▸ him
  obtain ⟨t, ht, hte⟩ := him'
  have hk : t⁻¹ * h ∈ qH.ker := by
    change qH (t⁻¹ * h) = 1
    rw [map_mul, map_inv, hte, inv_mul_cancel]
  have hh : h ∈ T := by
    have htm := T.mul_mem ht (hQT (hker ▸ hk))
    simpa only [mul_inv_cancel_left] using htm
  exact mem_map.mpr ⟨h, hh, rfl⟩

/-- The 14.7.67 centralizer implication with T-fixedness discharged from
the original flag plane and its actual cardinalities. The nonzero point
retains the preceding natural-quotient marking. -/
theorem source_plane_centralizer_le [Finite G]
    (a : ChapterJ.L2FourAction) (ρ : Representation (ZMod 2) H W)
    (qH : H →* ChapterJ.S5)
    (d : BinaryConjugationSection H U V₁ ρ)
    (p : ρ.IntertwiningMap (a.action.comp qH))
    (T : Sylow 2 H) (P : Sylow 2 ChapterJ.S5)
    (hTP : (T : Subgroup H).map qH = (P : Subgroup ChapterJ.S5))
    (hker : qH.ker = (H.pCoreIn 2).subgroupOf H)
    (hV₂U : V₂ ≤ U) (hV₁V₂ : V₁ ≤ V₂)
    (hV₁ : Nat.card V₁ = 2) (hV₂ : Nat.card V₂ = 4)
    (hTnorm : ∀ t : T, ((t : H) : G) ∈ normalizer (V₂ : Set G))
    (v : U) (hv₂ : (v : G) ∈ V₂)
    (hv : p (d.coordinates v).toAdd ≠ 0) :
    H ⊓ centralizer (V₂ : Set G) ≤ (T : Subgroup H).map H.subtype := by
  have hQT : (H.pCoreIn 2).subgroupOf H ≤ (T : Subgroup H) := by
    intro x hx
    obtain ⟨t, ht, htx⟩ := pCoreIn_le_sylow H T hx
    exact (H.subtype_injective htx) ▸ ht
  exact source_point_centralizer_le a ρ qH d p (T : Subgroup H) P hTP hker hQT v hv₂ hv
    (fun t => flag_plane_fixed ρ d hV₂U hV₁V₂ hV₁ hV₂ t (hTnorm t) v hv₂)

end PointCentralizer
end CFSG.Quasithin.Chapter14.Section07.LocalStructure
