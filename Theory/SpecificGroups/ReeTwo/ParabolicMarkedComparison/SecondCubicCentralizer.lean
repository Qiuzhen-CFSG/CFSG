module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicCensus
/-!
# The exact centralizer of the native cubic action

The central twist is constructed from the binary Frattini quotient and two
central roots. Together with the cubic and the eight fixed inner actors it
gives 48 distinct automorphisms. Their distinctness is checked on the single
cubic-orbit generator. The previously proved upper bound gives equality.

Source: the finite second-endpoint recognition in the binary Ree branch of
Aschbacher–Smith F.1.12, applied in J.4.5. The whole endpoint extension census
remains separate.
-/

@[expose] public section
noncomputable section
namespace ReeTwo.SylowModel.CubicAction
open Subgroup

abbrev V := Multiplicative (Fin 3 → ZMod 2)
/-- The native extra cubic-centralizing central twist. -/
def twistValue (v:V):A := generator 8 ^ (v.toAdd 1).val *
  generator 9 ^ (v.toAdd 0 + v.toAdd 1).val

def twistHom : V →* A where
  toFun := twistValue
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem twist_central (v:V) : twistHom v∈center A := by
  have hc : ∀(v:V)(i:Fin 3),twistHom v*orbit i=orbit i*twistHom v := by decide +kernel
  have hh:closure (Set.range orbit)≤centralizer ({twistHom v}:Set A) := by
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hc v i).symm
  rw [orbit_generated] at hh
  rw [mem_center_iff]
  intro a
  exact mem_centralizer_singleton_iff.mp (hh (mem_top a))

private theorem twist_square (v:V) : twistHom v*twistHom v=1 := by
  exact (by decide +kernel : ∀v:V,twistHom v*twistHom v=1) v

private theorem twist_quotient (v:V) : firstParabolicQuotient (twistHom v)=1 := by
  exact (by decide +kernel : ∀v:V,firstParabolicQuotient (twistHom v)=1) v

def twist : MulAut A where
  toFun a := a*twistHom (firstParabolicQuotient a)
  invFun a := a*twistHom (firstParabolicQuotient a)
  left_inv a := by
    simp only [map_mul,twist_quotient,mul_one,mul_assoc,twist_square]
  right_inv a := by
    simp only [map_mul,twist_quotient,mul_one,mul_assoc,twist_square]
  map_mul' a b := by
    simp only [map_mul]
    have hc := (mem_center_iff.mp (twist_central (firstParabolicQuotient a))) b
    calc
      a*b*(twistHom (firstParabolicQuotient a)*twistHom (firstParabolicQuotient b)) =
          a*(b*twistHom (firstParabolicQuotient a))*twistHom (firstParabolicQuotient b) := by group
      _ = a*(twistHom (firstParabolicQuotient a)*b)*twistHom (firstParabolicQuotient b) := by rw [hc]
      _ = a*twistHom (firstParabolicQuotient a)*(b*twistHom (firstParabolicQuotient b)) := by group

theorem cubic_orbit (i:Fin 3) : cubic (orbit i)=orbit (i+1) := by
  have h3:cubic^3=1 := cubic_order ▸ pow_orderOf_eq_one cubic
  fin_cases i
  · rw [orbit_actual,orbit_actual]
    rfl
  · rw [orbit_actual,orbit_actual]
    rfl
  · rw [orbit_actual,orbit_actual]
    change (cubic^3) ((generator 0)⁻¹)=(generator 0)⁻¹
    rw [h3]
    rfl

theorem twist_commutes_cubic : Commute twist cubic := by
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense orbit_generated
  rintro _ ⟨i,rfl⟩
  change twist (cubic (orbit i))=cubic (twist (orbit i))
  change cubic (orbit i)*twistHom (firstParabolicQuotient (cubic (orbit i)))=
    cubic (orbit i*twistHom (firstParabolicQuotient (orbit i)))
  rw [map_mul,cubic_orbit]
  congr 1
  change twistValue (firstParabolicQuotient (orbit (i+1)))=
    cubic (twistValue (firstParabolicQuotient (orbit i)))
  simp only [twistValue,map_mul,map_pow,cubic_generator]
  exact (by decide +kernel : ∀i:Fin 3,
    generator 8 ^ ((firstParabolicQuotient (orbit (i+1))).toAdd 1).val *
      generator 9 ^ ((firstParabolicQuotient (orbit (i+1))).toAdd 0+
        (firstParabolicQuotient (orbit (i+1))).toAdd 1).val =
    cubicImage 8 ^ ((firstParabolicQuotient (orbit i)).toAdd 1).val *
      cubicImage 9 ^ ((firstParabolicQuotient (orbit i)).toAdd 0+
        (firstParabolicQuotient (orbit i)).toAdd 1).val) i

theorem twist_square_eq_one : twist^2=1 := by
  apply MulEquiv.ext
  intro a
  exact twist.left_inv a


private def fixedCode (i:Fin 8):Nat := ![0,128,860,988,2360,2404,2488,2532] i
private def fixedElement (i:Fin 8):A := ⟨Collected.decode (fixedCode i),by
  rw [mem_firstParabolicCore_iff]
  exact (by decide +kernel : ∀i:Fin 8,(Collected.decode (fixedCode i)).left.b0=0) i⟩

private theorem fixedElement_fixed (i:Fin 8) : cubic (fixedElement i)=fixedElement i := by
  apply A.subtype_injective
  change (cubic (fixedElement i):SylowModel)=(fixedElement i:SylowModel)
  rw [←cubicEval_eq]
  exact (by decide +kernel : ∀i:Fin 8,cubicEval (fixedElement i)=(fixedElement i:SylowModel)) i

private theorem fixedElement_conj_commutes (i:Fin 8) : Commute (MulAut.conj (fixedElement i)) cubic := by
  apply MulEquiv.ext
  intro a
  simp only [MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,fixedElement_fixed]

private def candidate (i:Fin 8×Fin 3×Fin 2):MulAut A :=
  MulAut.conj (fixedElement i.1)*cubic^i.2.1.val*twist^i.2.2.val

private theorem candidate_commutes (i:Fin 8×Fin 3×Fin 2) : Commute (candidate i) cubic :=
  ((fixedElement_conj_commutes i.1).mul_left ((Commute.refl cubic).pow_left i.2.1.val)).mul_left
    (twist_commutes_cubic.pow_left i.2.2.val)

private def point (j:Fin 3) (k:Fin 2):A := if k=0 then orbit j else twist (orbit j)
private theorem candidate_point (i:Fin 8×Fin 3×Fin 2) :
    candidate i (orbit 0)=fixedElement i.1*point i.2.1 i.2.2*(fixedElement i.1)⁻¹ := by
  have hp (j:Fin 3) : (cubic^j.val) (orbit 0)=orbit j := by
    rw [orbit_actual j]
    rfl
  have hc:=DFunLike.congr_fun
    ((twist_commutes_cubic.pow_left i.2.2.val).pow_right i.2.1.val).eq (orbit 0)
  change (twist^i.2.2.val) ((cubic^i.2.1.val) (orbit 0))=
    (cubic^i.2.1.val) ((twist^i.2.2.val) (orbit 0)) at hc
  simp only [candidate,MulAut.mul_apply]
  rw [←hc,hp,MulAut.conj_apply]
  congr 2
  rcases i with ⟨i,j,k⟩
  fin_cases k <;> rfl

private def pointCode (j:Fin 3) (k:Fin 2):Nat := ![![1024,1536],![34,802],![2038,1782]] j k
private theorem point_code (j:Fin 3) (k:Fin 2):Collected.code (point j k)=pointCode j k := by
  exact (by decide +kernel : ∀j:Fin 3,∀k:Fin 2,Collected.code (point j k)=pointCode j k) j k

private def imageCode (i:Fin 8×Fin 3×Fin 2):Nat :=
  ![1024,1536,34,802,2038,1782,1280,1792,546,290,1270,1526,1680,1168,482,738,1062,1318,1936,1424,994,226,1830,1574,1360,1872,818,50,1590,1846,1216,1728,1010,242,2022,1766,1104,1616,306,562,1334,1078,1472,1984,498,754,1254,1510]
    ⟨6*i.1.val+2*i.2.1.val+i.2.2.val,by omega⟩

private theorem imageCode_injective : Function.Injective imageCode := by
  exact (by decide +kernel : ∀i j:Fin 8×Fin 3×Fin 2,imageCode i=imageCode j→i=j)

private theorem candidate_code (i:Fin 8×Fin 3×Fin 2) :
    Collected.code (candidate i (orbit 0):SylowModel)=imageCode i := by
  rw [candidate_point]
  change Collected.code (MulAut.conj (fixedElement i.1:SylowModel) (point i.2.1 i.2.2:SylowModel))=_
  rw [←Collected.packedConj_code,point_code]
  have hc (j:Fin 8):Collected.code (fixedElement j:SylowModel)=fixedCode j :=
    (by decide +kernel : ∀j:Fin 8,Collected.code (fixedElement j:SylowModel)=fixedCode j) j
  rw [hc]
  exact (by decide +kernel : ∀i:Fin 8×Fin 3×Fin 2,
    Collected.packedConj (fixedCode i.1) (pointCode i.2.1 i.2.2)=imageCode i) i

/-- The cubic-centralizing automorphism group has exactly forty-eight elements. -/
theorem cubic_centralizer_card : Nat.card {α:MulAut A // Commute α cubic}=48 := by
  apply Nat.le_antisymm CollectedBitVectors.cubic_commuting_aut_card_le
  let f:(Fin 8×Fin 3×Fin 2)→{α:MulAut A // Commute α cubic} :=
    fun i=>⟨candidate i,candidate_commutes i⟩
  have hf:Function.Injective f := by
    intro i j h
    apply imageCode_injective
    rw [←candidate_code i,←candidate_code j]
    exact congrArg (fun α:MulAut A=>Collected.code (α (orbit 0):SylowModel)) (congrArg Subtype.val h)
  have hcard:=Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod,Nat.card_fin] using hcard


/-- Every cubic-centralizing automorphism has the specified inner, cubic,
and central-twist factors. -/
theorem centralizer_factorization (α:MulAut A) (hα:Commute α cubic) :
    ∃a:A,cubic a=a ∧ ∃(j:Fin 3)(k:Fin 2),
      α=MulAut.conj a*cubic^j.val*twist^k.val := by
  let f:(Fin 8×Fin 3×Fin 2)→{α:MulAut A // Commute α cubic} :=
    fun i=>⟨candidate i,candidate_commutes i⟩
  have hf:Function.Injective f := by
    intro i j h
    apply imageCode_injective
    rw [←candidate_code i,←candidate_code j]
    exact congrArg (fun α:MulAut A=>Collected.code (α (orbit 0):SylowModel)) (congrArg Subtype.val h)
  have hb:Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr ⟨hf,by
    rw [cubic_centralizer_card]
    simp only [Nat.card_prod,Nat.card_fin]⟩
  obtain ⟨i,hi⟩:=hb.surjective ⟨α,hα⟩
  exact ⟨fixedElement i.1,fixedElement_fixed i.1,i.2.1,i.2.2,
    (congrArg Subtype.val hi).symm⟩

end ReeTwo.SylowModel.CubicAction
