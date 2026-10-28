module
public import Theory.Frattini.CentralElementarySupplement
public import Theory.Frattini.Intersection
public import Theory.GroupTheory.ElementaryPairInvolutionUnion
public import Theory.GroupTheory.ElementaryPairCommutator
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Conjugate core pairs with sharp element displacement

Let S be a finite two-subgroup, R = C_S(U), and U a central elementary
subgroup of R. Suppose every element outside R moves at least [S:R]
elements of U modulo its fixed subgroup. An automorphism of S moving U
outside R forces R and its image to be central elementary supplements
of their intersection. Their embedded Frattini subgroups agree and are
fixed by the automorphism.

When R is elementary, these two cores contain every involution of S.
An odd-order automorphism therefore preserves R. Only S is finite;
the common ambient group may be infinite.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (6.5), printed p.122. The faithful-amalgam and displacement
premises are discharged in DGS85/LocalStructure/CorePairDisplacement
and LinearNoncentralObstruction.
-/


open Subgroup
open scoped Pointwise IsMulCommutative
public noncomputable section
namespace Subgroup
variable {G : Type*} [Group G]

private theorem pair_saturation (S R U : Subgroup G) [Finite S]
    (hRS : R ≤ S) (hUS : U ≤ S) (hn : S ≤ normalizer (R : Set G))
    (hi : R.relIndex S ≤ R.relIndex U) : R ⊔ U = S := by
  let : Finite U := Finite.of_injective (inclusion hUS) (inclusion_injective _)
  have he : R.relIndex U = R.relIndex S := le_antisymm
    (relIndex_le_of_le_right hUS index_ne_zero_of_finite) hi
  have hm := relIndex_mul_relIndex R (R ⊔ U) S le_sup_left (sup_le hRS hUS)
  have heSup : R.relIndex (R ⊔ U) = R.relIndex U := by
    let : (R.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hn
    have hh := relIndex_sup_left (U.subgroupOf S) (R.subgroupOf S)
    rw [←subgroupOf_sup hRS hUS,relIndex_subgroupOf (sup_le hRS hUS),
      relIndex_subgroupOf hUS] at hh
    exact hh
  rw [heSup,he] at hm
  have hi0 : R.relIndex S ≠ 0 := index_ne_zero_of_finite
  have hh : (R ⊔ U).relIndex S = 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hi0) (hm.trans (mul_one _).symm)
  exact le_antisymm (sup_le hRS hUS) (relIndex_eq_one.mp hh)

private theorem pair_intersection (R U W : Subgroup G)
    (hUR : U ≤ R) (hspan : R ≤ U ⊔ W) (hn : U ≤ normalizer (W : Set G)) :
    R = U ⊔ (R ⊓ W) := by
  apply le_antisymm ?_ (sup_le hUR inf_le_left)
  intro r hr
  have hh : r ∈ (U : Set G) * (W : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right U W hn]
    exact hspan hr
  obtain ⟨u,hu,w,hw,rfl⟩ := hh
  have hwR : w ∈ R := by
    simpa only [inv_mul_cancel_left] using R.mul_mem (R.inv_mem (hUR hu)) hr
  exact mul_mem_sup hu ⟨hwR,hw⟩

private theorem pair_frattini (A D U : Subgroup G)
    [Finite A] (hp : IsPGroup 2 A) (he : IsElementaryAbelian 2 U)
    (hc : U ≤ centralizer (A : Set G)) (hA : A = U ⊔ D) :
    (frattini A).map A.subtype = (frattini D).map D.subtype := by
  have hDA : D ≤ A := hA ▸ le_sup_right
  have hUA : U ≤ A := hA ▸ le_sup_left
  let : IsElementaryAbelian 2 U := he
  let : IsElementaryAbelian 2 (U.subgroupOf A) := IsElementaryAbelian.subgroupOf hUA
  have hh := frattini_map_eq_of_central_elementary_supplement
    (⊤ : Subgroup A) (D.subgroupOf A) (U.subgroupOf A)
    (hp.to_subgroup ⊤) inferInstance
    (by intro u hu a _; exact Subtype.ext (hc hu a a.property))
    (by rw [←subgroupOf_sup hUA hDA,←hA,subgroupOf_self])
  have ht := frattini_image_map (⊤ : Subgroup A) A.subtype A.subtype_injective
  rw [←MonoidHom.range_eq_map,range_subtype] at ht
  have hD := frattini_image_map (D.subgroupOf A) A.subtype A.subtype_injective
  rw [map_subgroupOf_eq_of_le hDA] at hD
  exact ht.trans ((congrArg (Subgroup.map A.subtype) hh).trans hD.symm)

private theorem pair_centralizer_image (S R U : Subgroup G) (e : G ≃* G)
    (heS : S.map e.toMonoidHom = S) (hR : R = S ⊓ centralizer (U : Set G)) :
    R.map e.toMonoidHom = S ⊓ centralizer (U.map e.toMonoidHom : Set G) := by
  rw [hR,←map_inf_centralizer_of_injective _ e.injective,heS]

/-- Sharp element displacement forces both central supplements and fixes the
common Frattini image, with no restriction on the core index. -/
theorem centralizer_pair_frattini_of_displacement
    (S R U : Subgroup G) [Finite S] (e : G ≃* G)
    (hp : IsPGroup 2 S) (hU : IsElementaryAbelian 2 U)
    (hUR : U ≤ R) (hR : R = S ⊓ centralizer (U : Set G))
    (hn : S ≤ normalizer (R : Set G)) (heS : S.map e.toMonoidHom = S)
    (hb : ∀ a ∈ S, a ∉ R → R.relIndex S ≤ (centralizer ({a} : Set G)).relIndex U)
    (hout : ¬ U.map e.toMonoidHom ≤ R) :
    let R' := R.map e.toMonoidHom
    let D := R ⊓ R'
    R ⊔ R' = S ∧ R = U ⊔ D ∧ R' = U.map e.toMonoidHom ⊔ D ∧
      (frattini R).map R.subtype = (frattini D).map D.subtype ∧
      (frattini R').map R'.subtype = (frattini D).map D.subtype ∧
      ((frattini R).map R.subtype).map e.toMonoidHom = (frattini R).map R.subtype := by
  let R' := R.map e.toMonoidHom
  let U' := U.map e.toMonoidHom
  let D := R ⊓ R'
  have hRS : R ≤ S := hR ▸ inf_le_left
  have hR'S : R' ≤ S := (map_mono hRS).trans heS.le
  have hU'R' : U' ≤ R' := map_mono hUR
  let : Finite U := Finite.of_injective (inclusion (hUR.trans hRS)) (inclusion_injective _)
  let : Finite U' := Finite.of_injective (inclusion (hU'R'.trans hR'S)) (inclusion_injective _)
  have hR' : R' = S ⊓ centralizer (U' : Set G) := pair_centralizer_image S R U e heS hR
  have hn' : S ≤ normalizer (R' : Set G) := by
    have hh := map_mono (f := e.toMonoidHom) hn
    rw [heS,map_equiv_normalizer_eq] at hh
    exact hh
  have hUn : ¬ U ≤ R' := by
    intro hh
    apply hout
    rw [hR]
    exact le_inf (hU'R'.trans hR'S)
      (le_centralizer_iff.mp (hh.trans (hR' ▸ inf_le_right)))
  have hi' : R'.relIndex S = R.relIndex S := by
    change (R.map e.toMonoidHom).relIndex S = _
    conv_lhs => rhs; rw [←heS]
    exact relIndex_map_map_of_injective R S e.injective
  have hgen' : R' ⊔ U = S := by
    apply pair_saturation S R' U hR'S (hUR.trans hRS) hn'
    obtain ⟨a,ha,hao⟩ := SetLike.not_le_iff_exists.mp hout
    have hh := (hb a (hU'R'.trans hR'S ha) hao).trans
      (relIndex_le_of_le_left (centralizer_le (Set.singleton_subset_iff.mpr ha))
        (show (centralizer (U' : Set G)).relIndex U ≠ 0 from index_ne_zero_of_finite))
    have hcidx : R'.relIndex U = (centralizer (U' : Set G)).relIndex U := by
      change (R'.subgroupOf U).index = _
      congr 1
      ext u
      change (u : G) ∈ R' ↔ (u : G) ∈ centralizer (U' : Set G)
      rw [hR']
      exact and_iff_right ((hUR.trans hRS) u.property)
    rw [hi',hcidx]
    exact hh
  have hgen : R ⊔ U' = S := by
    apply pair_saturation S R U' hRS (hU'R'.trans hR'S) hn
    obtain ⟨a,ha,hao⟩ := SetLike.not_le_iff_exists.mp hUn
    have haS := hUR.trans hRS ha
    have haS' : e.symm a ∈ S := mem_map_equiv.mp (heS.symm ▸ haS)
    have hao' : e.symm a ∉ R := fun hh => hao (mem_map_equiv.mpr hh)
    have hh := hb (e.symm a) haS' hao'
    have hidx : (centralizer ({e.symm a} : Set G)).relIndex U =
        (centralizer ({a} : Set G)).relIndex U' := by
      conv_lhs => rw [←relIndex_map_map_of_injective (centralizer ({e.symm a} : Set G)) U
        (f := e.toMonoidHom) e.injective]
      congr 1
      ext z
      simp only [mem_map_equiv,mem_centralizer_singleton_iff]
      constructor <;> intro h <;> first
      | exact e.injective (by simpa only [map_mul,e.apply_symm_apply] using h)
      | simpa only [map_mul,e.apply_symm_apply] using congrArg e h
    rw [hidx] at hh
    have hle : R ≤ centralizer ({a} : Set G) :=
      (hR ▸ inf_le_right).trans (centralizer_le (Set.singleton_subset_iff.mpr ha))
    exact hh.trans (relIndex_le_of_le_left hle index_ne_zero_of_finite)
  have hRD : R = U ⊔ D := pair_intersection R U R' hUR
    (by rw [sup_comm,hgen']; exact hRS) ((hUR.trans hRS).trans hn')
  have hR'D : R' = U' ⊔ D := by
    simpa only [D,inf_comm] using pair_intersection R' U' R hU'R'
      (by rw [sup_comm,hgen]; exact hR'S) ((hU'R'.trans hR'S).trans hn)
  let : Finite R := Finite.of_injective (inclusion hRS) (inclusion_injective _)
  let : Finite R' := Finite.of_injective (inclusion hR'S) (inclusion_injective _)
  have hphi := pair_frattini R D U (hp.to_le hRS) hU
    (le_centralizer_iff.mp (hR ▸ inf_le_right)) hRD
  let := hU
  have hphi' := pair_frattini R' D U' (hp.to_le hR'S)
    (IsElementaryAbelian.map e.toMonoidHom)
    (le_centralizer_iff.mp (hR' ▸ inf_le_right)) hR'D
  refine ⟨le_antisymm (sup_le hRS hR'S)
    (hgen'.ge.trans (sup_le le_sup_right (hUR.trans le_sup_left))),hRD,hR'D,hphi,hphi',?_⟩
  exact (frattini_image_map R e.toMonoidHom e.injective).symm.trans (hphi'.trans hphi.symm)

/-- The two elementary cores exhaust all involutions. An odd automorphism
cannot exchange them, so it preserves the original core. -/
theorem centralizer_pair_fixed_of_odd
    (S R U : Subgroup G) [Finite S] (e : MulAut G)
    (hp : IsPGroup 2 S) (hU : IsElementaryAbelian 2 U)
    [IsElementaryAbelian 2 R]
    (hUR : U ≤ R) (hR : R = S ⊓ centralizer (U : Set G))
    (hn : S ≤ normalizer (R : Set G)) (heS : S.map e.toMonoidHom = S)
    (hb : ∀ a ∈ S, a ∉ R → R.relIndex S ≤ (centralizer ({a} : Set G)).relIndex U)
    (ho : Odd (orderOf e)) : R.map e.toMonoidHom = R := by
  by_cases hout : U.map e.toMonoidHom ≤ R
  · have hRS := hR ▸ (inf_le_left : S ⊓ centralizer (U : Set G) ≤ S)
    have hR'S := (map_mono hRS).trans heS.le
    let : Finite R := Finite.of_injective (inclusion hRS) (inclusion_injective _)
    have hc : R ≤ centralizer (U.map e.toMonoidHom : Set G) :=
      (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hout)
    have hle : R ≤ R.map e.toMonoidHom := by
      rw [pair_centralizer_image S R U e heS hR]
      exact le_inf hRS hc
    let : Finite (R.map e.toMonoidHom) :=
      Finite.of_injective (inclusion hR'S) (inclusion_injective _)
    exact (eq_of_le_of_card_ge hle (card_map_of_injective e.injective).le).symm
  obtain ⟨hgen,hRD,hR'D,_,_,_⟩ := centralizer_pair_frattini_of_displacement
    S R U e hp hU hUR hR hn heS hb hout
  let R' := R.map e.toMonoidHom
  let D := R ⊓ R'
  have hRS : R ≤ S := hR ▸ inf_le_left
  have hR'S : R' ≤ S := (map_mono hRS).trans heS.le
  let : Finite R := Finite.of_injective (inclusion hRS) (inclusion_injective _)
  let : Finite R' := Finite.of_injective (inclusion hR'S) (inclusion_injective _)
  let : Finite U := Finite.of_injective (inclusion hUR) (inclusion_injective _)
  let : IsElementaryAbelian 2 R' := IsElementaryAbelian.map _
  have hn' : S ≤ normalizer (R' : Set G) := by
    have hh := map_mono (f := e.toMonoidHom) hn
    rw [heS,map_equiv_normalizer_eq] at hh
    exact hh
  have hDc : D ≤ centralizer (S : Set G) := by
    rw [←hgen]
    exact inf_le_centralizer_sup_of_abelian R R'
  have hgenU : R' ⊔ U = S := le_antisymm (sup_le hR'S (hUR.trans hRS))
    (hgen.ge.trans (sup_le
      (hRD.le.trans (sup_le le_sup_right (inf_le_right.trans le_sup_left))) le_sup_left))
  have hi : R'.relIndex U = R.relIndex S := by
    have hh : R'.relIndex (R' ⊔ U) = R'.relIndex U := by
      let : (R'.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hn'
      have hh := relIndex_sup_left (U.subgroupOf S) (R'.subgroupOf S)
      rw [←subgroupOf_sup hR'S (hUR.trans hRS),
        relIndex_subgroupOf (sup_le hR'S (hUR.trans hRS)),
        relIndex_subgroupOf (hUR.trans hRS)] at hh
      exact hh
    rw [hgenU] at hh
    rw [←hh]
    conv_lhs => rhs; rw [←heS]
    exact relIndex_map_map_of_injective R S e.injective
  have hfix (v : G) (hv : v ∈ R') (hvo : v ∉ R)
      (u : G) (hu : u ∈ U) (hc : Commute v u) : u ∈ R' := by
    let C := U ⊓ centralizer ({v} : Set G)
    let E := U ⊓ R'
    have hEC : E ≤ C := by
      rintro a ⟨haU,haR⟩
      exact ⟨haU,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm (⟨a,haR⟩ : R') ⟨v,hv⟩))⟩
    have hiE : E.relIndex U = R.relIndex S := (inf_relIndex_left U R').trans hi
    have hiC : R.relIndex S ≤ C.relIndex U := by
      rw [inf_relIndex_left]
      exact hb v (hR'S hv) hvo
    have hm := relIndex_mul_relIndex E C U hEC inf_le_left
    rw [hiE] at hm
    have hpos : 0 < C.relIndex U := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hqpos : 0 < R.relIndex S := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have he1 : E.relIndex C = 1 := by
      have he0 : E.relIndex C ≠ 0 := by intro hz; rw [hz,zero_mul] at hm; omega
      nlinarith
    exact (relIndex_eq_one.mp he1 (show u ∈ C from
      ⟨hu,mem_centralizer_singleton_iff.mpr hc.symm.eq⟩)).2
  have hinvol : ∀ a ∈ S, a^2=1 → a ∈ R ∨ a ∈ R' := by
    apply elementary_pair_involution_union S R R' hgen (hR'S.trans hn)
    intro v hv hvo r hr hvr
    have hp : r ∈ (U : Set G) * (D : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right U D
        ((le_centralizer_iff.mp (hR ▸ inf_le_right)).trans
          ((centralizer_le inf_le_left).trans (centralizer_le_normalizer _))),←hRD]
      exact hr
    obtain ⟨u,hu,d,hd,rfl⟩ := hp
    have hud : Commute v u := by
      have hdc : Commute v d := hDc hd v (hR'S hv)
      simpa only [mul_inv_cancel_right] using hvr.mul_right hdc.inv_right
    exact R'.mul_mem (hfix v hv hvo u hu hud) hd.2
  let R'' := R'.map e.toMonoidHom
  let : IsElementaryAbelian 2 R'' := IsElementaryAbelian.map _
  have hR''S : R'' ≤ S := (map_mono hR'S).trans heS.le
  have hpair : R'' ≤ R ∨ R'' ≤ R' := le_one_of_elementwise_union R'' R R'
    (fun a ha => hinvol a (hR''S ha) (elemPow_eq_one_of_isElementaryAbelian a ha))
  have hc' : Nat.card R' = Nat.card R := card_map_of_injective e.injective
  have hc'' : Nat.card R'' = Nat.card R' := card_map_of_injective e.injective
  have htwo : R.map (e^2).toMonoidHom = R := by
    change R.map (e.toMonoidHom.comp e.toMonoidHom) = R
    rw [←map_map]
    rcases hpair with hh | hh
    · exact eq_of_le_of_card_ge hh (hc''.trans hc').ge
    · have hh' : R'' = R' := eq_of_le_of_card_ge hh hc''.ge
      have heR : R' = R := map_injective e.injective hh'
      exact hout ((map_mono hUR).trans heR.le) |>.elim
  have map_mul (f g : MulAut G) : R.map (f*g).toMonoidHom =
      (R.map g.toMonoidHom).map f.toMonoidHom := by rw [map_map]; rfl
  obtain ⟨m,hm⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one e) ho 1
  rw [pow_one] at hm
  rw [hm,pow_mul]
  clear hm
  induction m with
  | zero => change R.map (MonoidHom.id G) = R; exact map_id R
  | succ n ih => rw [pow_succ,map_mul,htwo,ih]

end Subgroup
