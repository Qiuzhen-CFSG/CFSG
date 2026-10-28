module
public import Theory.SpecificGroups.SymplecticFour.SmallRadicalInvariant
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Small normalized factors in a natural cover with its full fixed factor

Extend the natural projection from an embedded central cover across a
commuting fixed subgroup. The product map descends because the intersection
lies in the covering kernel. The image of a small normalized factor is a
small invariant set for the actual symplectic radical, so it is fixed.
Fixed-vector lifting in the cover then proves actual centralization upstairs.

Source: MS93 (3.7), printed p.872. The original input application is in
NonbinarySymplectic.OriginalStar.SmallFactors; no central attachment is removed.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
namespace Representation.SymplecticFourOrthogonalCover
variable {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
  {σ : Representation (ZMod 2) (L (K := F)) W}

theorem small_normal_factor_centralizes
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (D T J : Subgroup G) [Finite J]
    (hDU : D ≤ centralizer (j.range : Set G))
    (hDT : D ≤ centralizer (T : Set G))
    (hker : ∀ w, p w=0 ↔ j (Multiplicative.ofAdd w) ∈ D)
    (β : T →* L (K := F))
    (hβ : ((commutator (Sp F)).subtype.comp β).range.IsPRadical 2)
    (hact : ∀ t : T, ∀ w, j (Multiplicative.ofAdd (σ (β t) w))=
      (t:G)*j (Multiplicative.ofAdd w)*(t:G)⁻¹)
    (hJ : J ≤ j.range ⊔ D) (hTJ : T ≤ normalizer (J : Set G))
    (hcard : Nat.card J ≤ Nat.card F) : J ≤ centralizer (T : Set G) := by
  have hcomm (w : Multiplicative W) (d : D) : Commute (j w) (D.subtype d) := by
    exact hDU d.property _ ⟨w,rfl⟩
  let k := j.noncommCoprod D.subtype hcomm
  have hkr : k.range=j.range ⊔ D := by
    dsimp only [k]
    rw [MonoidHom.noncommCoprod_range,range_subtype]
  let q := k.rangeRestrict
  let f : Multiplicative W × D →* Multiplicative (Natural (K := F)) :=
    p.toLinearMap.toAddMonoidHom.toMultiplicative.comp (MonoidHom.fst _ _)
  have hk : q.ker ≤ f.ker := by
    intro x hx
    have he : j x.1*(x.2:G)=1 := congrArg Subtype.val hx
    have hd : j x.1 ∈ D := by
      rw [eq_inv_of_mul_eq_one_left he]
      exact D.inv_mem x.2.property
    exact (hker x.1.toAdd).mpr hd
  let π := q.liftOfSurjective k.rangeRestrict_surjective ⟨f,hk⟩
  have hπ (w : Multiplicative W) (d : D) :
      π (q (w,d))=Multiplicative.ofAdd (p w.toAdd) :=
    q.liftOfRightInverse_comp_apply _ _ _ _
  have hJK : J ≤ k.range := hJ.trans_eq hkr.symm
  let qJ := π.comp (inclusion hJK)
  let V : Set (Vector F) := {v | Multiplicative.ofAdd v ∈ qJ.range}
  have h0 : 0 ∈ V := qJ.range.one_mem
  have hc : Nat.card V ≤ Nat.card F := by
    let e : V ≃ qJ.range :=
      { toFun := fun v => ⟨Multiplicative.ofAdd v.val,v.property⟩
        invFun := fun v => ⟨v.val.toAdd,v.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    exact (Nat.card_le_card_of_surjective _ qJ.rangeRestrict_surjective).trans hcard
  have hπact (t : T) (x : k.range) :
      ∃ y : k.range, (y:G)=(t:G)*x*(t:G)⁻¹ ∧
        (π y).toAdd=binaryNatural (β t) (π x).toAdd := by
    obtain ⟨⟨w,d⟩,he⟩ := x.property
    have hx : x=q (w,d) := Subtype.ext he.symm
    subst x
    refine ⟨q (Multiplicative.ofAdd (σ (β t) w.toAdd),d),?_,?_⟩
    · change j (Multiplicative.ofAdd (σ (β t) w.toAdd))*(d:G)=
        (t:G)*(j w*(d:G))*(t:G)⁻¹
      rw [hact]
      change (t:G)*j w*(t:G)⁻¹*(d:G)=(t:G)*(j w*(d:G))*(t:G)⁻¹
      have hdt := hDT d.property (t:G)⁻¹ (T.inv_mem t.property)
      calc
        _ = (t:G)*j w*((t:G)⁻¹*d) := by group
        _ = (t:G)*j w*(d*(t:G)⁻¹) := by rw [hdt]
        _ = _ := by group
    · rw [hπ,hπ]
      exact LinearMap.congr_fun (p.isIntertwining' (β t)) w.toAdd
  have hV : ∀ a ∈ ((commutator (Sp F)).subtype.comp β).range,
      ∀ v ∈ V, a • v ∈ V := by
    rintro a ⟨t,rfl⟩ v ⟨x,hx⟩
    obtain ⟨y,hy,hyπ⟩ := hπact t (inclusion hJK x)
    have hyJ : (y:G) ∈ J := by
      rw [hy]
      exact (mem_normalizer_iff.mp (hTJ t.property) x).mp x.property
    refine ⟨⟨y,hyJ⟩,?_⟩
    change π y=Multiplicative.ofAdd (_ • v)
    apply Multiplicative.toAdd.injective
    rw [hyπ]
    have hv : (π (inclusion hJK x)).toAdd=v := congrArg Multiplicative.toAdd hx
    rw [hv]
    rfl
  have hfix := SmallRadicalInvariant.radical_fixes _ hβ hF hn V h0 hc hV
  intro x hx t ht
  obtain ⟨⟨w,d⟩,he⟩ := hJK hx
  have hxπ : π (q (w,d)) ∈ qJ.range :=
    ⟨⟨x,hx⟩,congrArg π (Subtype.ext he.symm)⟩
  have hv : p w.toAdd ∈ V := by rw [hπ] at hxπ; exact hxπ
  have hw := hfix _ ⟨⟨t,ht⟩,rfl⟩ _ hv
  have hf := cover_fixed_of_projection_fixed p hp (β ⟨t,ht⟩) w.toAdd hw
  have hj := hact ⟨t,ht⟩ w.toAdd
  rw [hf] at hj
  have htw : t*j w=j w*t := (mul_inv_eq_iff_eq_mul.mp hj.symm)
  have htd : t*(d:G)=(d:G)*t := hDT d.property t ht
  rw [←he]
  change t*(j w*(d:G))=(j w*(d:G))*t
  calc
    _ = (t*j w)*(d:G) := by group
    _ = (j w*t)*(d:G) := by rw [htw]
    _ = j w*(t*(d:G)) := by group
    _ = _ := by rw [htd]; group

end Representation.SymplecticFourOrthogonalCover
