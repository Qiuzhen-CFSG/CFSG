module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Duality
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Alternating

/-!
# The fixed binary plane inside Q/U

The Ru2 six-space coordinates send HC onto a subgroup of order four.
Normality of HC in H makes this image S₅-invariant. Its alternating-group
permutation action is trivial: simplicity of A₅ and 60 > 4! exclude an
injective action. Equivariance then gives [K,HC] ≤ U with the original
six-space quotient map. No classification of indecomposable modules is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(3), printed p.432 (PDF p.443).
-/

@[expose] public section
open Subgroup Representation
open scoped commutatorElement
noncomputable section
namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G] [Finite G]

private theorem alternating_action_four {X : Type*} [Finite X]
    (hX : Nat.card X = 4) (f : alternatingGroup (Fin 5) →* Equiv.Perm X) : f = 1 := by
  classical
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let := hs
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
  · have hi := (MonoidHom.ker_eq_bot_iff f).mp hb
    have hcard := Nat.card_le_card_of_injective f hi
    have ha : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup]; norm_num
    have hp : Nat.card (Equiv.Perm X) = 24 := by
      let := Fintype.ofFinite X
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hX]
      rfl
    omega
  · apply MonoidHom.ext
    intro a
    apply MonoidHom.mem_ker.mp
    rw [ht]
    trivial

def LocalSetup.hcSixMap (d : LocalSetup G) :
    d.toTypeRuSetup.HC →* Multiplicative SixSpace :=
  d.ru2.six.coordinates.comp (inclusion d.toTypeRuSetup.HC_le_Q)

theorem LocalSetup.hcSixMap_kernel (d : LocalSetup G) :
    d.hcSixMap.ker = d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.HC := by
  ext c
  exact d.ru2.six.coordinates_eq_one_iff (inclusion d.toTypeRuSetup.HC_le_Q c)

theorem LocalSetup.card_hcSixMap_range (d : LocalSetup G) :
    Nat.card d.hcSixMap.range = 4 := by
  have h := card_eq_card_quotient_mul_card_subgroup d.hcSixMap.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange d.hcSixMap).toEquiv,
    d.hcSixMap_kernel,
    Nat.card_congr (subgroupOfEquivOfLe d.U_le_HC).toEquiv,
    d.card_HC, d.ru2.card_U d.card_Z] at h
  omega

theorem LocalSetup.hcSixMap_invariant (d : LocalSetup G) (g : S5)
    (w : d.hcSixMap.range) :
    Multiplicative.ofAdd (d.ru2.sixAction g (w : Multiplicative SixSpace).toAdd) ∈
      d.hcSixMap.range := by
  obtain ⟨h, rfl⟩ := d.ru2.quotient_surjective g
  obtain ⟨c, hc⟩ := w.property
  have hn : d.toTypeRuSetup.H ≤ normalizer d.toTypeRuSetup.HC :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp d.toTypeRuSetup.HC_normal
  let c' : d.toTypeRuSetup.HC := ⟨h * c * (h : G)⁻¹,
    (mem_normalizer_iff.mp (hn h.property) c).mp c.property⟩
  refine ⟨c', ?_⟩
  apply Multiplicative.toAdd.injective
  have he := d.ru2.six.equivariant h (inclusion d.toTypeRuSetup.HC_le_Q c)
  change (d.hcSixMap c').toAdd = d.ru2.sixAction (d.ru2.quotientMap h)
    (d.hcSixMap c).toAdd at he
  rw [hc] at he
  exact he

def LocalSetup.hcSixAction (d : LocalSetup G) : S5 →* Equiv.Perm d.hcSixMap.range where
  toFun g := {
    toFun w := ⟨Multiplicative.ofAdd (d.ru2.sixAction g
      (w : Multiplicative SixSpace).toAdd), d.hcSixMap_invariant g w⟩
    invFun w := ⟨Multiplicative.ofAdd (d.ru2.sixAction g⁻¹
      (w : Multiplicative SixSpace).toAdd), d.hcSixMap_invariant g⁻¹ w⟩
    left_inv w := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      change d.ru2.sixAction g⁻¹ (d.ru2.sixAction g _) = _
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    right_inv w := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      change d.ru2.sixAction g (d.ru2.sixAction g⁻¹ _) = _
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl }
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp [map_mul]

theorem LocalSetup.HC_commutator_K_mem_U (d : LocalSetup G)
    (c : d.toTypeRuSetup.HC) (k : d.toTypeRuSetup.K) :
    ⁅(k : G), (c : G)⁆ ∈ d.toTypeRuSetup.U := by
  have ht := alternating_action_four d.card_hcSixMap_range
    (d.hcSixAction.comp (alternatingGroup (Fin 5)).subtype)
  let h : d.toTypeRuSetup.H := inclusion d.toTypeRuSetup.K_le_H k
  let q : d.toTypeRuSetup.Q := inclusion d.toTypeRuSetup.HC_le_Q c
  let q' : d.toTypeRuSetup.Q := ⟨h * q * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.ru2.six.normalized h.property) q).mp q.property⟩
  have hfix : d.ru2.sixAction (d.ru2.quotientMap h) (d.hcSixMap c).toAdd =
      (d.hcSixMap c).toAdd := by
    have hh := congrArg (fun f : alternatingGroup (Fin 5) →* Equiv.Perm d.hcSixMap.range =>
      ((f (d.toTypeRuSetup.alternatingMap k) ⟨d.hcSixMap c, ⟨c, rfl⟩⟩ :
        d.hcSixMap.range) : Multiplicative SixSpace)) ht
    exact congrArg Multiplicative.toAdd hh
  have he : d.ru2.six.coordinates q' = d.ru2.six.coordinates q := by
    apply Multiplicative.toAdd.injective
    exact (d.ru2.six.equivariant h q).trans hfix
  have hk := (d.ru2.six.coordinates_eq_one_iff (q' * q⁻¹)).mp
    (by rw [map_mul, map_inv, he, mul_inv_cancel])
  exact hk

end CFSG.Quasithin.ChapterJ
