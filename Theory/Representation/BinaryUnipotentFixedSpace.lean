module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.Representation.DualCommutator

/-!
# Timmesfeld's fixed-space argument over the binary field

Suppose the fixed space of an opposite two-group is a line and its positive
unipotent orbit spans the module. The Levi orbit of that line is simple:
every nonzero invariant subspace has an opposite-unipotent fixed vector.
The orbit span supplements the radical commutators. Applied to the dual,
this gives a nondegenerate evaluation pairing from the radical fixed space
into a simple contragredient module, proving its irreducibility.

The subgroup containments and the fixed-line/cyclicity statements remain
explicit hypotheses. No splitting field or absolute irreducibility is used.
The concrete consumer is the binary SL5 end-parabolic application in
`EndNode.Levi.Irreducibility`.

Source: Timmesfeld's proof of Smith's theorem, GLS, Volume 3, Theorem 2.8.11,
`refs/KGroup/GLS3/chapter2.tex`, pp.95–96.
-/

@[expose] public section
namespace Representation.BinaryUnipotentFixedSpace
open BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

def orbitSpan (L : Subgroup G) (z : V) : Subrepresentation (ρ.comp L.subtype) where
  toSubmodule := Submodule.span (ZMod 2) (Set.range fun l : L => ρ l z)
  apply_mem_toSubmodule l := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, rfl⟩ := hv
      exact Submodule.subset_span ⟨l * a, by simp [Module.End.mul_apply]⟩
    | zero => simp
    | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
    | smul c v _ hv => simpa only [map_smul] using Submodule.smul_mem _ c hv

theorem mem_orbitSpan (L : Subgroup G) (z : V) : z ∈ orbitSpan ρ L z := by
  exact Submodule.subset_span ⟨1, by simp⟩

theorem orbitSpan_le (L : Subgroup G) (z : V)
    (W : Subrepresentation (ρ.comp L.subtype)) (hz : z ∈ W) : orbitSpan ρ L z ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  exact W.apply_mem_toSubmodule l hz

theorem orbitSpan_fixed (L S : Subgroup G) (hLS : L ≤ Subgroup.normalizer (S : Set G)) (z : V)
    (hz : z ∈ invariants (ρ.comp S.subtype)) :
    (orbitSpan ρ L z).toSubmodule ≤ invariants (ρ.comp S.subtype) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩ s
  have hs : (l : G)⁻¹ * s * l ∈ S :=
    (Subgroup.mem_normalizer_iff''.mp (hLS l.property) s).mp s.property
  have hh := hz ⟨_, hs⟩
  change ρ s (ρ l z) = ρ l z
  calc
    _ = ρ l (ρ ((l : G)⁻¹ * s * l) z) := by simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
    _ = ρ l z := congrArg (ρ l) hh

/-- A unique fixed line makes its Levi orbit span simple. -/
theorem orbitSpan_irreducible [Finite G] [FiniteDimensional (ZMod 2) V]
    (L S T : Subgroup G) (hT : IsPGroup 2 T) (hLS : L ≤ Subgroup.normalizer (S : Set G))
    (hST : S ≤ T) (hTSL : T ≤ S ⊔ L) (z : V) (hz0 : z ≠ 0)
    (hz : z ∈ invariants (ρ.comp T.subtype))
    (hline : invariants (ρ.comp T.subtype) ≤ Submodule.span (ZMod 2) {z}) :
    IsIrreducible (orbitSpan ρ L z).toRepresentation := by
  apply (Subrepresentation.irreducible_iff_isAtom _).mpr
  refine ⟨?_, ?_⟩
  · intro he
    have hm := mem_orbitSpan ρ L z
    rw [he] at hm
    exact hz0 hm
  · intro W hW
    by_contra hW0
    have hfix : W.toSubmodule ≤ invariants (ρ.comp S.subtype) :=
      le_trans hW.le (orbitSpan_fixed ρ L S hLS z (fun s => hz ⟨s, hST s.property⟩))
    have hstable : T ≤ subspaceStabilizer ρ W.toSubmodule := by
      apply hTSL.trans
      apply sup_le
      · apply le_subspaceStabilizer
        intro s hs w hw
        rw [show ρ s w = w from hfix hw ⟨s, hs⟩]
        exact hw
      · apply le_subspaceStabilizer
        intro l hl w hw
        exact W.apply_mem_toSubmodule ⟨l, hl⟩ hw
    have hWbot : W.toSubmodule ≠ ⊥ := fun h => hW0 (Subrepresentation.toSubmodule_injective h)
    let : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hWbot
    let τ : Representation (ZMod 2) T W.toSubmodule :=
      (stabilizerRepresentation ρ W.toSubmodule).comp (Subgroup.inclusion hstable)
    obtain ⟨v, hv0, hv⟩ := pGroup_fix_nonzero_vector
      (F := ZMod 2) (by simp [ZMod.ringChar_zmod_n])
      (by simpa only [ZMod.ringChar_zmod_n] using hT) τ
    have hvfixed : (v : V) ∈ invariants (ρ.comp T.subtype) := by
      intro t
      exact congrArg Subtype.val (hv t)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hline hvfixed)
    have hc0 : c ≠ 0 := by
      intro he
      subst c
      simp only [zero_smul] at hc
      exact hv0 (Subtype.ext hc.symm)
    have hzW : z ∈ W := by
      have hh := W.toSubmodule.smul_mem c⁻¹ v.property
      rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at hh
      exact hh
    exact (not_le_of_gt hW) (orbitSpan_le ρ L z W hzW)

theorem commutator_stable (R L : Subgroup G)
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) (l : L) :
    Coinvariants.ker (ρ.comp R.subtype) ≤
      (Coinvariants.ker (ρ.comp R.subtype)).comap (ρ l) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨r, v⟩, rfl⟩
  have hr : (l : G) * r * l⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp (hLR l.property) r).mp r.property
  have hm := Coinvariants.sub_mem_ker (ρ := ρ.comp R.subtype) ⟨_, hr⟩ (ρ l v)
  change ρ l (ρ r v - v) ∈ Coinvariants.ker (ρ.comp R.subtype)
  change ρ ((l : G) * r * l⁻¹) (ρ l v) - ρ l v ∈ _ at hm
  have he : ρ ((l : G) * r * l⁻¹) (ρ l v) = ρ l (ρ r v) := by
    simp only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel, mul_one]
  rw [he] at hm
  simpa only [map_sub] using hm

/-- The Levi orbit of an opposite cyclic vector surjects onto radical coinvariants. -/
theorem commutator_sup_orbitSpan (R L U : Subgroup G)
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) (hU : U ≤ R ⊔ L) (z : V)
    (hspan : Submodule.span (ZMod 2) (Set.range fun u : U => ρ u z) = ⊤) :
    Coinvariants.ker (ρ.comp R.subtype) ⊔ (orbitSpan ρ L z).toSubmodule = ⊤ := by
  let C := Coinvariants.ker (ρ.comp R.subtype)
  let W := (orbitSpan ρ L z).toSubmodule
  let Q := C ⊔ W
  have hstable : U ≤ subspaceStabilizer ρ Q := by
    apply hU.trans
    apply sup_le
    · apply le_subspaceStabilizer
      intro r hr v hv
      have hd : ρ r v - v ∈ Q := (show C ≤ Q from le_sup_left) (Coinvariants.sub_mem_ker
        (ρ := ρ.comp R.subtype) ⟨r, hr⟩ v)
      simpa only [sub_add_cancel] using Q.add_mem hd hv
    · apply le_subspaceStabilizer
      intro l hl v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      have ha' : ρ l a ∈ Q := (show C ≤ Q from le_sup_left)
        (commutator_stable ρ R L hLR ⟨l, hl⟩ ha)
      have hb' : ρ l b ∈ Q := (show W ≤ Q from le_sup_right)
        ((orbitSpan ρ L z).apply_mem_toSubmodule ⟨l, hl⟩ hb)
      simpa only [map_add] using Q.add_mem ha' hb'
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨u, rfl⟩
  exact (hstable u.property z).mpr ((show W ≤ Q from le_sup_right) (mem_orbitSpan ρ L z))

/-- The normalizing subgroup acts on the literal radical invariants. -/
noncomputable def fixedSubrepresentation (R L : Subgroup G)
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) :
    Subrepresentation (ρ.comp L.subtype) where
  toSubmodule := invariants (ρ.comp R.subtype)
  apply_mem_toSubmodule l v hv r := by
    have hr : (l : G)⁻¹ * r * l ∈ R :=
      (Subgroup.mem_normalizer_iff''.mp (hLR l.property) r).mp r.property
    have hh := hv ⟨_, hr⟩
    change ρ r (ρ l v) = ρ l v
    calc
      _ = ρ l (ρ ((l : G)⁻¹ * r * l) v) := by
        simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
      _ = ρ l v := congrArg (ρ l) hh

/-- Restriction of evaluation to an invariant subspace of the contragredient. -/
def fixedPairing (R L : Subgroup G) (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (W : Subrepresentation (ρ.dual.comp L.subtype)) :
    IntertwiningMap (fixedSubrepresentation ρ R L hLR).toRepresentation
      W.toRepresentation.dual where
  toLinearMap := {
    toFun v := {
      toFun f := (f : Module.Dual (ZMod 2) V) (v : V)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    map_add' v w := by ext f; exact map_add f.val v.val w.val
    map_smul' c v := by ext f; exact map_smul f.val c v.val }
  isIntertwining' l := by
    ext v f
    change f.val (ρ l v.val) = f.val (ρ ((l⁻¹ : L) : G)⁻¹ v.val)
    simp only [Subgroup.coe_inv, inv_inv]

/-- Spanning modulo the radical commutators makes the restricted pairing nondegenerate. -/
theorem fixedPairing_injective (R L : Subgroup G)
    (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (W : Subrepresentation (ρ.dual.comp L.subtype))
    (hspan : Coinvariants.ker (ρ.dual.comp R.subtype) ⊔ W.toSubmodule = ⊤) :
    Function.Injective (fixedPairing ρ R L hLR W) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  apply Subtype.ext
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) v.val).mp
  intro f
  have hvC : v.val ∈ (Coinvariants.ker (ρ.dual.comp R.subtype)).dualCoannihilator := by
    exact (invariants_eq_dual_commutator_coannihilator (ρ.comp R.subtype)) ▸ v.property
  have hf : f ∈ Coinvariants.ker (ρ.dual.comp R.subtype) ⊔ W.toSubmodule := by
    rw [hspan]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
  rw [Submodule.mem_dualCoannihilator] at hvC
  have hza : a v.val = 0 := hvC a ha
  have hzb : b v.val = 0 := LinearMap.congr_fun hv ⟨b, hb⟩
  change a v.val + b v.val = 0
  rw [hza, hzb, add_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Timmesfeld's binary fixed-space argument, with the Curtis inputs explicit. -/
theorem fixedSubrepresentation_irreducible [Finite G] [FiniteDimensional (ZMod 2) V]
    [Nontrivial V] (R L S U T : Subgroup G)
    (hR : IsPGroup 2 R) (hT : IsPGroup 2 T)
    (hLR : L ≤ Subgroup.normalizer (R : Set G))
    (hLS : L ≤ Subgroup.normalizer (S : Set G))
    (hST : S ≤ T) (hTSL : T ≤ S ⊔ L) (hURL : U ≤ R ⊔ L)
    (z : Module.Dual (ZMod 2) V) (hz0 : z ≠ 0)
    (hz : z ∈ invariants (ρ.dual.comp T.subtype))
    (hline : invariants (ρ.dual.comp T.subtype) ≤ Submodule.span (ZMod 2) {z})
    (hspan : Submodule.span (ZMod 2) (Set.range fun u : U => ρ.dual u z) = ⊤) :
    IsIrreducible (fixedSubrepresentation ρ R L hLR).toRepresentation := by
  let W : Subrepresentation (ρ.dual.comp L.subtype) := orbitSpan ρ.dual L z
  let : IsIrreducible W.toRepresentation := by
    exact orbitSpan_irreducible ρ.dual L S T hT hLS hST hTSL z hz0 hz hline
  let : IsIrreducible W.toRepresentation.dual := by
    exact isIrreducible_dual (k := ZMod 2) (G := L) (V := W.toSubmodule)
      (ρ := W.toRepresentation)
  obtain ⟨v, hv0, hv⟩ := pGroup_fix_nonzero_vector
    (F := ZMod 2) (by simp [ZMod.ringChar_zmod_n])
    (by simpa only [ZMod.ringChar_zmod_n] using hR) (ρ.comp R.subtype)
  let : Nontrivial (fixedSubrepresentation ρ R L hLR).toSubmodule :=
    ⟨⟨⟨v, hv⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  exact RepMap.irreducible_of_inj (f := fixedPairing ρ R L hLR W)
    (fixedPairing_injective ρ R L hLR W
      (commutator_sup_orbitSpan ρ.dual R L U hLR hURL z hspan))

end Representation.BinaryUnipotentFixedSpace
