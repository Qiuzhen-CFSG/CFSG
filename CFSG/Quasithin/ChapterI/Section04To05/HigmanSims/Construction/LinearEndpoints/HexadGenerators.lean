module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadAction

/-!
# Original generators of the linear and hexad groups

The endpoint is maximal in each original overgroup. The linear marking
supplies one maximality, while the simple alternating-six quotient and its
minimum permutation degree supply the other. Every specified exterior
element therefore generates the corresponding whole original overgroup
with the endpoint.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F
local notation "A6" => alternatingGroup (Fin 6)

/-- The retained endpoint is maximal in the literal alternating-six preimage. -/
theorem NaturalEndpointData.hexad_endpoint_isCoatom (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier ≤ L) (e : L ≃* Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom = Point) :
    IsCoatom (d.carrier.subgroupOf d.hexad_overgroup) := by
  obtain ⟨_,_,_,_,_,π,hπs,hπker,_⟩ := d.hexad_overgroup_structure L hPL e hmark
  let D := d.hexad_overgroup
  let P := d.carrier.subgroupOf D
  have hPi : P.index=6 := d.hexad_endpoint_index L hPL e hmark
  have hker : π.ker≤P := hπker ▸ fun _ hx => d.kernel_le hx
  change IsCoatom P
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨?_,?_⟩
  · intro ht
    rw [ht,index_top] at hPi
    contradiction
  · intro R hR hPR
    let T := R.map π
    have hRT : T.comap π=R := comap_map_eq_self (hker.trans hPR)
    have hT : T≠⊤ := by
      intro he
      apply hR
      rw [←hRT,he,comap_top]
    have hi : T.index=R.index := R.index_map_eq hπs (hker.trans hPR)
    let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
    have hd := T.card_dvd_factorial_index_of_simple hT
    have hc : Nat.card A6=360 := by rw [nat_card_alternatingGroup,Nat.card_fin]; decide
    rw [hc,hi] at hd
    have hlow : 6≤R.index := by
      by_contra hh
      have hh' : R.index≤5 := by omega
      interval_cases he : R.index <;> norm_num [he,Nat.factorial] at hd
    have hm := P.relIndex_mul_index hPR
    rw [hPi] at hm
    have hp : 0<P.relIndex R := Nat.pos_of_ne_zero (by intro he; rw [he,zero_mul] at hm; omega)
    have he : P.relIndex R=1 := by nlinarith
    exact relIndex_eq_one.mp he

/-- Specified exterior elements generate both whole original groups with
the retained endpoint, preserving the actual join in the ambient group. -/
theorem NaturalEndpointData.exterior_elements_generate_overgroups (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier≤L) (e : L≃*Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom=Point)
    (ell n : G) (hell : ell∈L) (hellP : ell∉d.carrier)
    (hn : n∈d.hexad_overgroup) (hnP : n∉d.carrier) :
    d.carrier⊔zpowers ell=L ∧ d.carrier⊔zpowers n=d.hexad_overgroup ∧
      (d.carrier⊔zpowers ell)⊔zpowers n=L⊔d.hexad_overgroup := by
  obtain ⟨_,_,hPD,_⟩ := d.hexad_overgroup_structure L hPL e hmark
  have hmaxL : IsCoatom (d.carrier.subgroupOf L) :=
    (e.mapSubgroup.isCoatom_iff _).mp (by
      change IsCoatom ((d.carrier.subgroupOf L).map e.toMonoidHom)
      rw [hmark]
      exact Matrix.PSL3.LinearThree.pointParabolic_isCoatom _)
  have join_eq (H : Subgroup G) (hPH : d.carrier≤H)
      (hmax : IsCoatom (d.carrier.subgroupOf H)) (x : G) (hx : x∈H) (hxP : x∉d.carrier) :
      d.carrier⊔zpowers x=H := by
    let J := d.carrier⊔zpowers x
    have hJH : J≤H := sup_le hPH (zpowers_le.mpr hx)
    have hPJ : d.carrier.subgroupOf H≤J.subgroupOf H :=
      fun _ hy => (show d.carrier≤J from le_sup_left) hy
    have htop : J.subgroupOf H=⊤ := by
      rcases hmax.le_iff.mp hPJ with ht | he
      · exact ht
      · have hm : (⟨x,hx⟩:H)∈J.subgroupOf H :=
          (show zpowers x≤J from le_sup_right) (mem_zpowers x)
        rw [he] at hm
        exact (hxP hm).elim
    have hh := congrArg (Subgroup.map H.subtype) htop
    simpa only [map_subgroupOf_eq_of_le hJH,←MonoidHom.range_eq_map,range_subtype] using hh
  have hL := join_eq L hPL hmaxL ell hell hellP
  have hD := join_eq d.hexad_overgroup hPD (d.hexad_endpoint_isCoatom L hPL e hmark) n hn hnP
  refine ⟨hL,hD,?_⟩
  rw [hL,←hD,←sup_assoc,sup_eq_left.mpr hPL]

end CFSG.Quasithin.HigmanSims
