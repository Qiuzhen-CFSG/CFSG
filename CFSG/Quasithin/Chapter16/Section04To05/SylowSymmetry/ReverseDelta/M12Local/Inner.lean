module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M12Consequences
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Theory.Mathieu.M12.Properties.AutCover


/-!
# The M₁₂ projection and the noncentral covering lift

The actual A₅ residual image embeds in the centralizer of the projected inner
involution. It excludes the solvable quaternion-extension row of 16.1.5(4).
The remaining C₂ × S₅ row has Sylow index greater than two, so that involution
is not central in any Sylow two-subgroup. Only then is I.2.2(5b) applied.
The resulting lift gives an actual commuting factorization in the ambient
group. With trivial center, transport identifies the full relative centralizer.

The exact earlier involution table and lifting clause remain explicit inputs.
They are owned by the existing Chapter 16 and Chapter I table developments;
this module does not assert those source results or repeat involution fusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 16.4.11(2), printed p.1193; 16.1.5(4), p.1171;
I.2.2(5b), pp.409–410. Residuals mean O² throughout.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.M12Local
open Subgroup Theory.GroupTheory
open DoubleCoverCentralizer
open CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

private theorem a5_not_solvable : ¬ Group.IsSolvable ReverseDelta.A5 := by
  let : Group.IsPerfect ReverseDelta.A5 :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable _

/-- The A₅ image in the comparison embeds in the actual projected centralizer. -/
private noncomputable def residualImageHom (d : Contrary T z L g R r)
    (l : L) (hl : L.normalizerMonoidHom
      ⟨r, d.setup.sylow_normalizes (d.setup.le_sylow d.mem)⟩ = MulAut.conj l)
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M12) :
    centralImage L (residual L r) →*
      (MulAut.conj (e (QuotientGroup.mk' (center L) l))).fixedSubgroup where
  toFun x := ⟨e x, by
    rw [MulAut.fixedSubgroup_conj, mem_centralizer_singleton_iff]
    obtain ⟨y, hy, hyx⟩ := x.property
    change y ∈ (residual L r).subgroupOf L at hy
    have hc : (y : G) ∈ centralizer ({r} : Set G) := (residual_le L r hy).2
    have he : MulAut.conj l y = y := by
      rw [← hl]
      apply Subtype.ext
      change r * (y : G) * r⁻¹ = y
      rw [← mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
    have hycomm : y * l = l * y := by
      have hh : l * y * l⁻¹ = y := he
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    rw [← hyx, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hycomm]⟩
  map_one' := Subtype.ext (map_one e)
  map_mul' x y := Subtype.ext (map_mul e (x : L ⧸ center L) (y : L ⧸ center L))

/-- The table's solvable row is excluded by the actual A₅ residual image. -/
theorem projected_centralizer (d : Contrary T z L g R r)
    (hc : M12Comparison L (L.conjBy g) r z)
    (htable : ∀ a : MulAut Sporadic.Mathieu.M12, orderOf a = 2 →
      M12InvolutionAlternative a)
    (l : L) (hl : L.normalizerMonoidHom
      ⟨r, d.setup.sylow_normalizes (d.setup.le_sylow d.mem)⟩ = MulAut.conj l)
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M12) :
    orderOf (QuotientGroup.mk' (center L) l) = 2 ∧
    Nonempty ((MulAut.conj (e (QuotientGroup.mk' (center L) l))).fixedSubgroup ≃*
      InnerCentralizerModel) := by
  have ho : orderOf (QuotientGroup.mk' (center L) l) = 2 := by
    rw [← orderOf_injective (quotientConj (H := L)) quotientConj_injective,
      quotientConj_mk, ← hl]
    exact d.inner_action_order
  have hao : orderOf (MulAut.conj (e (QuotientGroup.mk' (center L) l))) = 2 := by
    rw [MulAut.conj_orderOf_of_center_eq_bot Sporadic.Mathieu.m12_center_eq_bot,
      e.orderOf_eq, ho]
  refine ⟨ho, ?_⟩
  rcases htable _ hao with ⟨_, hq | hp⟩ | ⟨hn, _⟩
  · let f := residualImageHom d l hl e
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    let := quaternionExtension_solvable hq
    let := Group.isSolvable_of_isSolvable_injective (f := f) hf
    obtain ⟨j⟩ := hc.innerResidual
    exact (a5_not_solvable (Group.isSolvable_of_surjective (f := j.toMonoidHom) j.surjective)).elim
  · exact hp
  · exact (hn ⟨_, rfl⟩).elim

/-- A product-row involution is non-2-central in the actual central quotient. -/
theorem projection_not_twoCentral (d : Contrary T z L g R r)
    (hc : M12Comparison L (L.conjBy g) r z)
    (htable : ∀ a : MulAut Sporadic.Mathieu.M12, orderOf a = 2 →
      M12InvolutionAlternative a)
    (l : L) (hl : L.normalizerMonoidHom
      ⟨r, d.setup.sylow_normalizes (d.setup.le_sylow d.mem)⟩ = MulAut.conj l)
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M12) :
    ¬ TwoCentral (QuotientGroup.mk' (center L) l) := by
  obtain ⟨ho, hp⟩ := projected_centralizer d hc htable l hl e
  rintro ⟨S, hu, hcen⟩
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hle : (P : Subgroup Sporadic.Mathieu.M12) ≤
      (MulAut.conj (e (QuotientGroup.mk' (center L) l))).fixedSubgroup := by
    rintro _ ⟨s, hs, rfl⟩
    rw [MulAut.fixedSubgroup_conj, mem_centralizer_singleton_iff]
    change e s * e _ = e _ * e s
    rw [← map_mul, ← map_mul]
    exact congrArg e (congrArg Subtype.val ((mem_center_iff.mp hcen) ⟨s, hs⟩))
  have hindex := m12_product_fixed_sylow_index _ (Or.inl hp) P
  rw [relIndex_eq_one.mpr hle] at hindex
  omega

/-- Equality of the actual inner actions gives the commuting ambient factor. -/
theorem factor_of_inner_action (d : Contrary T z L g R r)
    (l : L) (hl : L.normalizerMonoidHom
      ⟨r, d.setup.sylow_normalizes (d.setup.le_sylow d.mem)⟩ = MulAut.conj l) :
    r * (l : G)⁻¹ ∈ centralizer (L : Set G) := by
  let rn : normalizer (L : Set G) :=
    ⟨r, d.setup.sylow_normalizes (d.setup.le_sylow d.mem)⟩
  let ln : normalizer (L : Set G) := ⟨l, L.le_normalizer l.property⟩
  have he : L.normalizerMonoidHom ln = MulAut.conj l := by ext x; rfl
  have hk : rn * ln⁻¹ ∈ L.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he]
    change L.normalizerMonoidHom rn * (MulAut.conj l)⁻¹ = 1
    rw [show L.normalizerMonoidHom rn = MulAut.conj l from hl, mul_inv_cancel]
  rw [normalizerMonoidHom_ker] at hk
  exact hk

/-- I.2.2(5b) is applied only after proving the non-2-central mark. -/
theorem cover_lift (d : Contrary T z L g R r)
    (hc : M12Comparison L (L.conjBy g) r z)
    (htable : ∀ a : MulAut Sporadic.Mathieu.M12, orderOf a = 2 →
      M12InvolutionAlternative a)
    (hlift : center L ≠ ⊥ → NonTwoCentralInvolutionLifting L)
    (hZ : center L ≠ ⊥) :
    ∃ c ∈ centralizer (L : Set G), ∃ l ∈ L, r = c * l ∧ orderOf l = 4 := by
  obtain ⟨l, hl⟩ := d.inner_action
  obtain ⟨e⟩ := hc.component
  have ho := (projected_centralizer d hc htable l hl e).1
  obtain ⟨f, hf, hf4⟩ := hlift hZ _ ho (projection_not_twoCentral d hc htable l hl e)
  have hact : MulAut.conj f = MulAut.conj l := congrArg quotientConj hf
  refine ⟨r * (f : G)⁻¹, factor_of_inner_action d f (hl.trans hact.symm),
    f, f.property, ?_, ?_⟩
  · group
  · exact (orderOf_injective L.subtype L.subtype_injective f).trans hf4

/-- With trivial center the full relative centralizer is C₂ × S₅. -/
theorem inner_centralizer (d : Contrary T z L g R r)
    (hc : M12Comparison L (L.conjBy g) r z)
    (htable : ∀ a : MulAut Sporadic.Mathieu.M12, orderOf a = 2 →
      M12InvolutionAlternative a)
    (hZ : center L = ⊥) :
    Nonempty ((L ⊓ centralizer ({r} : Set G) : Subgroup G) ≃* InnerCentralizerModel) := by
  obtain ⟨l, hl⟩ := d.inner_action
  obtain ⟨e⟩ := hc.component
  obtain ⟨j⟩ := (projected_centralizer d hc htable l hl e).2
  let q : L ≃* (L ⧸ center L) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center L))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hZ]),
        QuotientGroup.mk'_surjective _⟩
  let a := L.normalizerMonoidHom
    ⟨r, d.setup.sylow_normalizes (d.setup.le_sylow d.mem)⟩
  have he : MulAut.congr (q.trans e) a =
      MulAut.conj (e (QuotientGroup.mk' (center L) l)) := by
    rw [show a = MulAut.conj l from hl, MulAut.congr_conj]
    rfl
  let k := MulAut.fixedSubgroupCongr (q.trans e) a
  exact ⟨(normalizerFixedEquivCentralizer L _).symm.trans
    (k.trans ((MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup he)).trans j))⟩
end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.M12Local
