module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCoordinates
public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.PairOrders
public import Theory.GroupTheory.PrimeOrderLift
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.NormalizerCubicCentralizer

/-!
# The original canonical pair in the same alternating-six quotient

The literal canonical pair has orders three and four and product order five.
The full elementary kernel preserves odd orders. The natural SL2(4) quotient
has no element of order four, so the second image is an involution. Thus the
same original hexad quotient receives an actual marked (3,2,5) pair.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "A6" => alternatingGroup (Fin 6)

private theorem four_power (x : Representation.SL2FourNatural.SL) (hx : x^4=1) : x^2=1 := by
  have hall : ∀ x : Representation.SL2FourNatural.SL, x^4=1 → x^2=1 := by decide +kernel
  exact hall x hx

/-- The actual marked pair maps to orders three and two with product order
five under the same full-kernel hexad quotient. -/
theorem NaturalEndpointData.hexad_pair_quotient_orders (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier≤L) (e : L≃*Matrix.PSL3Four.PSL)
    (hPD : d.carrier≤d.hexad_overgroup)
    (q : d.hexad_overgroup→*A6) (hqker : q.ker=A.subgroupOf d.hexad_overgroup)
    (p : Fin 2→d.carrier)
    (hp : ∀ i,e (inclusion hPL (p i))=Matrix.PSL3Four.MathieuAmalgamMarking.pair i) :
    orderOf (q (inclusion hPD (p 0)))=3 ∧
      orderOf (q (inclusion hPD (p 1)))=2 ∧
      orderOf (q (inclusion hPD (p 0))*q (inclusion hPD (p 1)))=5 := by
  have horders := Matrix.PSL3Four.MathieuAmalgamMarking.canonical_pair_orders
  have h0 : orderOf (p 0)=3 := by
    rw [←orderOf_injective (inclusion hPL) (inclusion_injective hPL),←e.orderOf_eq,hp]
    exact horders.1
  have h1 : orderOf (p 1)=4 := by
    rw [←orderOf_injective (inclusion hPL) (inclusion_injective hPL),←e.orderOf_eq,hp]
    exact horders.2.1
  have h01 : orderOf (p 0*p 1)=5 := by
    rw [←orderOf_injective (inclusion hPL) (inclusion_injective hPL),←e.orderOf_eq,map_mul,map_mul,hp,hp]
    exact horders.2.2
  let X := inclusion hPD (p 0)
  let Y := inclusion hPD (p 1)
  have hX : orderOf X=3 := (orderOf_injective (inclusion hPD) (inclusion_injective hPD) _).trans h0
  have hY : orderOf Y=4 := (orderOf_injective (inclusion hPD) (inclusion_injective hPD) _).trans h1
  have hXY : orderOf (X*Y)=5 := by
    change orderOf (inclusion hPD (p 0)*inclusion hPD (p 1))=5
    rw [←map_mul,orderOf_injective (inclusion hPD) (inclusion_injective hPD)]
    exact h01
  have hk : IsPGroup 2 q.ker := by
    rw [hqker]
    exact (IsElementaryAbelian.isPGroup (p:=2) (G:=A)).comap_subtype
  have hqX : orderOf (q X)=3 := (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk X
    (by rw [hX];decide)).trans hX
  have hqXY : orderOf (q (X*Y))=5 := (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk (X*Y)
    (by rw [hXY];decide)).trans hXY
  have hs2 : (d.quotient (p 1))^2=1 := four_power _ (by
    rw [←map_pow,show (p 1)^4=1 from h1 ▸ pow_orderOf_eq_one (p 1),map_one])
  have hy2A : ((p 1:G)^2)∈A := by
    have hh : (p 1)^2∈d.quotient.ker := by rw [MonoidHom.mem_ker,map_pow,hs2]
    rwa [d.quotient_kernel] at hh
  have hqY2 : (q Y)^2=1 := by
    rw [←map_pow]
    change Y^2∈q.ker
    rw [hqker]
    exact hy2A
  have hqY1 : q Y≠1 := by
    intro hh
    have ha : (p 1:G)∈A := show Y∈A.subgroupOf d.hexad_overgroup from hqker ▸ hh
    have hy2 : Y^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) _ ha)
    have hd := orderOf_dvd_of_pow_eq_one hy2
    rw [hY] at hd
    norm_num at hd
  exact ⟨hqX,orderOf_eq_prime hqY2 hqY1,by simpa only [map_mul] using hqXY⟩


/-- A cubic in the original natural endpoint acts without nonzero fixed
vectors through its unchanged hexad quotient and whole-kernel coordinates. -/
theorem NaturalEndpointData.hexad_cubic_kernel_fixed_free (d : NaturalEndpointData A)
    (hPD : d.carrier≤d.hexad_overgroup)
    (q : d.hexad_overgroup→*A6) (hqker : q.ker=A.subgroupOf d.hexad_overgroup)
    (k : q.ker≃*Multiplicative Theory.SpecificGroups.SymmetricSix.NaturalModule)
    (hk : ∀ (g : d.hexad_overgroup) (a : q.ker),
      k (MulAut.conjNormal g a)=Multiplicative.ofAdd
        (Theory.SpecificGroups.SymmetricSix.polarAction (q g).val (k a).toAdd))
    (t : d.carrier) (ht3 : orderOf t=3) :
    ∀ v : Theory.SpecificGroups.SymmetricSix.NaturalModule,
      Theory.SpecificGroups.SymmetricSix.polarAction (q (inclusion hPD t)).val v=v → v=0 := by
  intro v hv
  let a : q.ker := k.symm (Multiplicative.ofAdd v)
  have hvk : (k a).toAdd=v := by simp [a]
  have hfix : MulAut.conjNormal (inclusion hPD t) a=a := by
    apply k.injective
    rw [hk,hvk,hv]
    exact (k.apply_symm_apply _).symm
  have hcomm : Commute ((a:d.hexad_overgroup):G) (t:G) := by
    have hh := congrArg (fun x : q.ker => ((x:d.hexad_overgroup):G)) hfix
    change (t:G)*((a:d.hexad_overgroup):G)*(t:G)⁻¹=((a:d.hexad_overgroup):G) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have haA : ((a:d.hexad_overgroup):G)∈A :=
    show (a:d.hexad_overgroup)∈A.subgroupOf d.hexad_overgroup from hqker ▸ a.property
  have hz : ((a:d.hexad_overgroup):G)∈(⊥:Subgroup G) :=
    d.cubic_radical_centralizer t t.property ((orderOf_coe t).trans ht3) ▸
      (show ((a:d.hexad_overgroup):G)∈A⊓centralizer ({(t:G)}:Set G) from
        ⟨haA,mem_centralizer_singleton_iff.mpr hcomm.eq⟩)
  have ha : a=1 := Subtype.ext (Subtype.ext (mem_bot.mp hz))
  rw [←hvk,ha,map_one]
  rfl

end CFSG.Quasithin.HigmanSims
