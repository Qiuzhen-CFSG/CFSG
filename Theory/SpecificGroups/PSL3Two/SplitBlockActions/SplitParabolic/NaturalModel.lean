module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair

/-!
# The genuine split natural binary block and its middle radical

A complement to V, a quotient isomorphism L/V = SL3(2), and an equivariant
identification of V with the natural column module give an actual group
isomorphism L = E8 ⋊ SL3(2). Its projection is the original quotient map.

For the middle radical, published coordinates (13,14,23,24) are realized
by translation (14,13,0) and matrix I + 24 E02 + 23 E12. This is the
natural column convention obtained from the upper-unitriangular row/dual
convention by inverse transpose and reversal of the three coordinates.
The translation e2 is the row involution. The upper transvection E01 and
the displayed order-three matrix act as column and columnCubic. In this
natural convention U belongs to the point parabolic and the second
parabolic is the line stabilizer, for the incident flag e0 in v2=0.
The full compatible Sylow identification and generator exhaustion remain
separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007.
-/

@[expose] public section
set_option synthInstance.maxSize 512

namespace Matrix.PSL3Two.SplitParabolic
abbrev E3 := Multiplicative (Fin 3 → ZMod 2)
def naturalAction : SL →* MulAut E3 where
 toFun g := (SpecialLinearGroup.toLin' g).toAddEquiv.toMultiplicative
 map_one' := by
  ext v : 1
  change SpecialLinearGroup.toLin' 1 v.toAdd = v.toAdd
  rw [map_one]
  rfl
 map_mul' g h := by
  ext v : 1
  change SpecialLinearGroup.toLin' (g*h) v.toAdd =
    SpecialLinearGroup.toLin' g (SpecialLinearGroup.toLin' h v.toAdd)
  rw [map_mul]
  rfl
abbrev Block := E3 ⋊[naturalAction] SL
def projection : Block →* SL := SemidirectProduct.rightHom
def standardSylow : Subgroup Block := borelSL.comap projection
def pointPreimage : Subgroup Block := pointParabolicSL.comap projection
def linePreimage : Subgroup Block := lineParabolicSL.comap projection

/-- Natural column coordinates obtained by inverse transpose and reversal
from the (13,14,23,24) middle radical. -/
def middleElement (v : BinaryFourSplitPair.E) : Block :=
 ⟨Multiplicative.ofAdd ![v.toAdd 1, v.toAdd 0, 0],
  ⟨!![1,0,v.toAdd 3; 0,1,v.toAdd 2; 0,0,1], by simp [Matrix.det_fin_three]⟩⟩

def middleMap : BinaryFourSplitPair.E →* Block where
 toFun := middleElement
 map_one' := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i; fin_cases i <;> rfl
  · apply Subtype.ext; decide +kernel
 map_mul' := by
  intro v w
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    revert v w i
    decide +kernel
  · apply Subtype.ext
    change (middleElement (v*w)).right.val = (middleElement v * middleElement w).right.val
    revert v w
    decide +kernel

def middleGroup : Subgroup Block := middleMap.range

def readMiddle (g : Block) : BinaryFourSplitPair.E :=
 Multiplicative.ofAdd ![g.left.toAdd 1, g.left.toAdd 0, g.right.val 1 2, g.right.val 0 2]

theorem readMiddle_middleMap (v : BinaryFourSplitPair.E) : readMiddle (middleMap v) = v := by
 apply Multiplicative.toAdd.injective
 funext i
 fin_cases i <;> rfl

theorem middleMap_injective : Function.Injective middleMap :=
 Function.LeftInverse.injective readMiddle_middleMap

noncomputable def middleCoordinates : middleGroup ≃* BinaryFourSplitPair.E :=
 (MonoidHom.ofInjective middleMap_injective).symm

theorem middleCoordinates_apply (v : BinaryFourSplitPair.E) :
 middleCoordinates ⟨middleMap v, ⟨v,rfl⟩⟩ = v :=
 (MonoidHom.ofInjective middleMap_injective).symm_apply_apply v

theorem middleGroup_card : Nat.card middleGroup = 16 :=
 (Nat.card_congr middleCoordinates.toEquiv).trans BinaryFourSplitPair.card_E

def rowLift : Block := SemidirectProduct.inl (Multiplicative.ofAdd ![0,0,1])
def columnLift : Block := SemidirectProduct.inr ⟨!![1,1,0;0,1,0;0,0,1],by decide⟩
def cubicLift : Block := SemidirectProduct.inr ⟨!![1,1,0;1,0,0;0,0,1],by decide⟩

theorem rowLift_action : ∀ v, rowLift * middleMap v * rowLift⁻¹ =
 middleMap (BinaryFourSplitPair.row v) := by
 intro v
 apply SemidirectProduct.ext
 · apply Multiplicative.toAdd.injective
   funext i; revert v i; decide +kernel
 · apply Subtype.ext
   change (rowLift * middleMap v * rowLift⁻¹).right.val = (middleMap (BinaryFourSplitPair.row v)).right.val
   revert v
   decide +kernel
theorem columnLift_action : ∀ v, columnLift * middleMap v * columnLift⁻¹ =
 middleMap (BinaryFourSplitPair.column v) := by
 intro v
 apply SemidirectProduct.ext
 · apply Multiplicative.toAdd.injective
   funext i; revert v i; decide +kernel
 · apply Subtype.ext
   change (columnLift * middleMap v * columnLift⁻¹).right.val = (middleMap (BinaryFourSplitPair.column v)).right.val
   revert v
   decide +kernel
theorem cubicLift_action : ∀ v, cubicLift * middleMap v * cubicLift⁻¹ =
 middleMap (BinaryFourSplitPair.columnCubic v) := by
 intro v
 apply SemidirectProduct.ext
 · apply Multiplicative.toAdd.injective
   funext i; revert v i; decide +kernel
 · apply Subtype.ext
   change (cubicLift * middleMap v * cubicLift⁻¹).right.val = (middleMap (BinaryFourSplitPair.columnCubic v)).right.val
   revert v
   decide +kernel

variable {L : Type*} [Group L] (V : Subgroup L) [V.Normal]
structure SplitNaturalData where
 quotient : (L ⧸ V) ≃* SL
 moduleEquiv : V ≃* E3
 equivariant : ∀ (g : L) (v : V),
  moduleEquiv ⟨g * v * g⁻¹, (inferInstance : V.Normal).conj_mem v v.property g⟩ =
    naturalAction (quotient (QuotientGroup.mk' V g)) (moduleEquiv v)
 complement : Subgroup L
 splitting : V.IsComplement' complement
namespace SplitNaturalData
variable {V} (d : SplitNaturalData V)
noncomputable def complementEquiv : d.complement ≃* SL :=
 d.splitting.symm.QuotientMulEquiv.symm.trans d.quotient

theorem complementEquiv_apply (c : d.complement) :
 d.complementEquiv c = d.quotient (QuotientGroup.mk' V (c : L)) := rfl

noncomputable def blockEquiv : L ≃* Block :=
 (SemidirectProduct.mulEquivSubgroup d.splitting).symm.trans
  (SemidirectProduct.congr d.moduleEquiv d.complementEquiv (by
    intro c
    apply MulEquiv.ext
    intro v
    exact d.equivariant c v))

theorem blockEquiv_projection (g : L) :
 projection (d.blockEquiv g) = d.quotient (QuotientGroup.mk' V g) := by
 obtain ⟨x,rfl⟩ := (SemidirectProduct.mulEquivSubgroup d.splitting).surjective g
 dsimp only [blockEquiv, MulEquiv.trans_apply]
 rw [MulEquiv.symm_apply_apply]
 change d.complementEquiv x.right = d.quotient (QuotientGroup.mk' V ((x.left : L) * x.right))
 rw [map_mul, map_mul]
 have h0 : QuotientGroup.mk' V (x.left : L) = 1 := (QuotientGroup.eq_one_iff _).mpr x.left.property
 rw [h0, map_one, one_mul]
 rfl
/-- The constructed isomorphism preserves every marked quotient preimage. -/
theorem preimage_map (P : Subgroup SL) :
 (P.comap (d.quotient.toMonoidHom.comp (QuotientGroup.mk' V))).map
   d.blockEquiv.toMonoidHom = P.comap projection := by
 ext g
 obtain ⟨g,rfl⟩ := d.blockEquiv.surjective g
 constructor
 · rintro ⟨x,hx,he⟩
   have h : x=g := d.blockEquiv.injective he
   subst x
   change projection (d.blockEquiv g) ∈ P
   rw [d.blockEquiv_projection]
   exact hx
 · intro hg
   refine ⟨g,?_,rfl⟩
   change projection (d.blockEquiv g) ∈ P at hg
   rw [d.blockEquiv_projection] at hg
   exact hg

end SplitNaturalData
end Matrix.PSL3Two.SplitParabolic
