module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.TorusFusion

/-!
# The elementary centralizer of the original four-group torus

The outer involution fixes an elementary four in the quaternion core.
Its full centralizer in H has relative index two over that four: the
quaternion-core quotient has order eighteen, and the previously proved
torus-centralizer calculation excludes three. The outer involution is a
central complement, so the whole torus centralizer is elementary of order
eight. Its full normalizer has order forty-eight by the six-element action.

These are statements about the original I.4(G1)–(G2) configuration. They
bound the order of a product of endpoint reflections in MaximalWeylProduct;
no Atlas realization or ambient recognition is assumed. Source:
Aschbacher–Smith I.4.5, printed p.417, continuing the four-group calculation
in Fong–Wong §3A, Nagoya Math. J.36 (1969), p.155.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
omit [Finite G] in
private theorem torus_centralizer_map (t : CubicTorus c) :
    (Subgroup.centralizer ({t.n}:Set c.H)).map c.H.subtype =
      Subgroup.centralizer (t.torus.map c.H.subtype:Set G) := by
  apply le_antisymm
  · rintro _ ⟨u,hu,rfl⟩ v ⟨w,hw,rfl⟩
    change ((w*u:c.H):G)=((u*w:c.H):G)
    apply congrArg Subtype.val
    have hz : Commute t.z u := Subtype.ext
      (mem_centralizer_singleton_iff.mp (t.centralizer ▸ u.property)).symm
    have hn : Commute t.n u := (mem_centralizer_singleton_iff.mp hu).symm
    have ht : t.torus ≤ Subgroup.centralizer ({u}:Set c.H) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hz))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hn))
    exact mem_centralizer_singleton_iff.mp (ht hw)
  · intro u hu
    have hzA : (t.z:G)∈t.torus.map c.H.subtype :=
      mem_map_of_mem _ (mem_sup_left (mem_zpowers _))
    have hnA : (t.n:G)∈t.torus.map c.H.subtype :=
      mem_map_of_mem _ (mem_sup_right (mem_zpowers _))
    have huH : u∈c.H := t.centralizer.ge
      (mem_centralizer_singleton_iff.mpr (hu _ hzA).symm)
    exact ⟨⟨u,huH⟩,mem_centralizer_singleton_iff.mpr (Subtype.ext (hu _ hnA).symm),rfl⟩

private theorem core_outer_fixed_four (t : CubicTorus c) :
    IsElementaryAbelian 2 ((Subgroup.centralizer ({t.n}:Set c.H)).subgroupOf (quaternionCore c)) ∧
    Nat.card ((Subgroup.centralizer ({t.n}:Set c.H)).subgroupOf (quaternionCore c))=4 := by
  let Q := quaternionCore c
  let d := quaternionCoreData c
  let a : MulAut Q := MulAut.conjNormal t.n
  have ha : a^2=1 := by
    change (MulAut.conjNormal t.n : MulAut Q)^2=1
    rw [←map_pow,show t.n^2=1 from t.n_order ▸ pow_orderOf_eq_one t.n,map_one]
  have ho := outside_bothOuter c t.n t.outside
  have hf := quaternion_central_product_outer_involution d.left d.right
    d.left_model d.right_model d.span d.intersection_card d.commute a ha
    ho.left_map ho.right_map ho.left_outer ho.right_outer
  have he : a.toMonoidHom.eqLocus (MonoidHom.id Q)=
      (Subgroup.centralizer ({t.n}:Set c.H)).subgroupOf Q := by
    ext q
    change a q=q ↔ _
    rw [mem_subgroupOf,mem_centralizer_singleton_iff]
    constructor
    · intro h
      have hh : t.n*(q:c.H)*t.n⁻¹=(q:c.H) := congrArg Subtype.val h
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro h
      apply Subtype.ext
      change t.n*(q:c.H)*t.n⁻¹=(q:c.H)
      rw [←h,mul_inv_cancel_right]
  rw [he] at hf
  exact ⟨hf.1,hf.2.1⟩

/-- The pointwise centralizer of the original torus is elementary of order eight. -/
theorem torus_centralizer_structure (t : CubicTorus c) :
    IsElementaryAbelian 2 (Subgroup.centralizer (t.torus.map c.H.subtype:Set G)) ∧
    Nat.card (Subgroup.centralizer (t.torus.map c.H.subtype:Set G))=8 := by
  let C := Subgroup.centralizer ({t.n}:Set c.H)
  let Q := quaternionCore c
  have hno : ¬3∣Nat.card C := by
    rw [←card_map_of_injective c.H.subtype_injective,t.torus_centralizer_map]
    exact t.three_not_dvd_torus_centralizer
  have hi18 : Q.relIndex C∣18 := quaternionCore_index c ▸ relIndex_dvd_index_of_normal Q C
  have hi3 : ¬3∣Q.relIndex C := fun h=>hno (h.trans (relIndex_dvd_card Q C))
  have hi2 : Q.relIndex C∣2 :=
    ((Nat.prime_three.coprime_iff_not_dvd.mpr hi3).symm.pow_right 2).dvd_of_dvd_mul_left hi18
  have hnQ : t.n∉Q := fun h=>t.outside
    ((sup_le_sup (c.H₁.pCoreIn_le 2) (c.H₂.pCoreIn_le 2)) h)
  have hnC : t.n∈C := mem_centralizer_singleton_iff.mpr rfl
  have hi : Q.relIndex C=2 := (Nat.prime_two.eq_one_or_self_of_dvd _ hi2).resolve_left (by
    intro h
    exact hnQ ((relIndex_eq_one.mp h) hnC))
  have hfc : Nat.card (Q.subgroupOf C)=4 := by
    have he : Q.subgroupOf C=(Q⊓C).subgroupOf C := (inf_subgroupOf_right Q C).symm
    rw [he,Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv,
      inf_comm,←Nat.card_congr (subgroupOfEquivOfLe (show C⊓Q≤Q from inf_le_right)).toEquiv]
    simpa only [inf_subgroupOf_right] using t.core_outer_fixed_four.2
  have hcc : Nat.card C=8 := by
    have hh := (Q.subgroupOf C).card_mul_index
    change Nat.card (Q.subgroupOf C)*Q.relIndex C=Nat.card C at hh
    rw [hfc,hi] at hh
    exact hh.symm
  have hqpow (u : c.H) (huQ : u∈Q) (huC : u∈C) : u^2=1 := by
    let : IsElementaryAbelian 2 (C.subgroupOf Q) := t.core_outer_fixed_four.1
    exact congrArg (fun w : Q => (w:c.H))
      (elemPow_eq_one_of_isElementaryAbelian (A:=C.subgroupOf Q) (⟨u,huQ⟩:Q) huC)
  have hpow (u : C) : u^2=1 := by
    apply Subtype.ext
    by_cases huQ : (u:c.H)∈Q
    · exact hqpow u huQ u.property
    · have hun : (u:c.H)*t.n∈Q :=
        ((Q.subgroupOf C).mul_mem_iff_of_index_two hi (a:=u) (b:=⟨t.n,hnC⟩)).mpr (by
          change (u:c.H)∈Q ↔ t.n∈Q
          simp only [huQ,hnQ])
      have hsq := hqpow ((u:c.H)*t.n) hun (C.mul_mem u.property hnC)
      have hcomm : Commute (u:c.H) t.n := mem_centralizer_singleton_iff.mp u.property
      rw [hcomm.mul_pow,show t.n^2=1 from t.n_order ▸ pow_orderOf_eq_one t.n,mul_one] at hsq
      exact hsq
  have hC : IsElementaryAbelian 2 C := {
    toIsMulCommutative := ⟨⟨fun u v => by
      have hiu : u⁻¹=u := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpow u)
      have hiv : v⁻¹=v := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpow v)
      have hiuv : (u*v)⁻¹=u*v := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hpow (u*v))
      simpa only [mul_inv_rev,hiu,hiv] using hiuv.symm⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  rw [←t.torus_centralizer_map]
  let := hC
  exact ⟨IsElementaryAbelian.map c.H.subtype,by rw [card_map_of_injective c.H.subtype_injective,hcc]⟩
/-- The full normalizer of the original torus has order forty-eight. -/
theorem torus_normalizer_card (t : CubicTorus c) :
    Nat.card (normalizer (t.torus.map c.H.subtype:Set G))=48 := by
  let A := t.torus.map c.H.subtype
  let C := Subgroup.centralizer (A:Set G)
  let N := normalizer (A:Set G)
  have hh := relIndex_mul_relIndex (⊥:Subgroup G) C N bot_le (centralizer_le_normalizer (A:Set G))
  simp only [relIndex_bot_left] at hh
  rw [t.torus_centralizer_structure.2,t.ambient_torus_normalizer_index] at hh
  exact hh.symm

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
