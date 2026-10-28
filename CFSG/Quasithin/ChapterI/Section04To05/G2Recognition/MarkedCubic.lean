module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicFusion
public import Theory.GroupTheory.SL23CubicEightObstruction

/-!
# The marked M supplies a third cubic class

No cubic element of either original SL₂(3) factor normalizes an elementary
eight. Applying this to the literal conjugates of F*(M) shows that such an
element lies in no conjugate of M. Thus the cubic elements supplied by the
actual PSL₃(2) quotient of M belong to neither factor class, even under
ambient conjugacy. The same exclusion holds for their cyclic lines.
The order-192 marked overlap supplies a cubic that can be conjugated inside
H into the original plane of order nine, on neither factor line.

This uses the actual normal elementary eight and the actual factor
embeddings in Aschbacher–Smith (G1)–(G2), printed p.417. It supplies a new
marked fusion obstruction for the exceptional q=3 argument; Fong–Wong
§4D explicitly excludes q₁=q₂=3, and Fong70 §6 refers this case to Janko.
The Sylow-nine and order-27-core exclusions, BN-pair recognition and
Atlas model comparison remain with `qt-i45-g2-recognition`.
`Chapter14MarkedCubic` applies the result to the original SourceLocalData.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal
  G2ThreeConfiguration.V_normal V_elementary

/-- A cubic in the first marked factor cannot normalize any elementary eight. -/
theorem cubic_factor_not_normalizes_eight (x : c.H₁) (hx : orderOf x=3)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : Nat.card E=8) :
    ((x:c.H):G) ∉ normalizer (E : Set G) := by
  obtain ⟨z,hz,_,hH⟩ := exists_marked_involution c
  obtain ⟨P,_,eP⟩ := cubic_quaternion_sylow c x hx
  exact no_elementary_eight_normalized_by_sl23_cubic c.H c.H₁ c.H₁_model.some
    z hz hH x hx P eP.some E hE

/-- The marked factor cubic lies in no conjugate of the actual M. -/
theorem cubic_factor_not_mem_conjugate_M (x : c.H₁) (hx : orderOf x=3) (g : G) :
    ((x:c.H):G) ∉ c.M.map (MulAut.conj g).toMonoidHom := by
  rintro ⟨m,hm,he⟩
  let A := c.V.map c.M.subtype
  let E := A.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hE : Nat.card E=8 := by
    rw [card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective c.M.subtype_injective,V_card c]
  have hmN : m ∈ normalizer (A : Set G) := by
    apply c.V.le_normalizer_map c.M.subtype
    exact mem_map_of_mem c.M.subtype (show (⟨m,hm⟩ : c.M) ∈ normalizer (c.V : Set c.M) by
      rw [normalizer_eq_top]; trivial)
  apply cubic_factor_not_normalizes_eight c x hx E hE
  exact he ▸ A.le_normalizer_map (MulAut.conj g).toMonoidHom (mem_map_of_mem _ hmN)

/-- Every element of the marked M avoids the cubic class of the first factor. -/
theorem cubic_factor_not_conjugate_M (x : c.H₁) (hx : orderOf x=3) (m : c.M) :
    ¬ IsConj ((x:c.H):G) (m:G) := by
  intro h
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  apply cubic_factor_not_mem_conjugate_M c x hx g⁻¹
  refine ⟨m,m.property,?_⟩
  change g⁻¹*(m:G)*(g⁻¹)⁻¹=((x:c.H):G)
  rw [←hg]
  group

/-- The marked factor line cannot be carried to a line in the actual M. -/
theorem cubic_factor_line_not_conjugate_M (x : c.H₁) (hx : orderOf x=3)
    (m : c.M) (g : G) :
    (zpowers ((x:c.H):G)).map (MulAut.conj g).toMonoidHom ≠ zpowers (m:G) := by
  intro he
  have hm : MulAut.conj g ((x:c.H):G) ∈ c.M := by
    apply (zpowers_le.mpr m.property : zpowers (m:G) ≤ c.M)
    rw [←he]
    exact mem_map_of_mem _ (mem_zpowers _)
  exact cubic_factor_not_conjugate_M c x hx ⟨_,hm⟩ (isConj_iff.mpr ⟨g,rfl⟩)

/-- The original factors and the original M supply three distinct cubic classes. -/
theorem exists_three_marked_cubic_classes (x : c.H₁) (y : c.H₂)
    (hx : orderOf x=3) (hy : orderOf y=3) :
    ∃ m : c.M, orderOf m=3 ∧
      ¬ IsConj ((x:c.H):G) ((y:c.H):G) ∧
      ¬ IsConj ((x:c.H):G) (m:G) ∧ ¬ IsConj ((y:c.H):G) (m:G) := by
  obtain ⟨m,hm⟩ := exists_prime_orderOf_dvd_card' (G := c.M) 3 (by rw [M_card c]; decide)
  exact ⟨m,hm,cubic_factors_not_conjugate c x y hx hy,
    cubic_factor_not_conjugate_M c x hx m,
    cubic_factor_not_conjugate_M (swapFactors c) y hy m⟩

/-- A conjugate of an actual M-cubic lies in the common plane, outside both
marked factor lines. No ambient Sylow-nine assumption is used. -/
theorem exists_marked_M_diagonal (x : c.H₁) (y : c.H₂)
    (hx : orderOf x=3) (hy : orderOf y=3) :
    ∃ (m : c.M) (g : G), orderOf m=3 ∧
      MulAut.conj g (m:G) ∈ zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G) ∧
      MulAut.conj g (m:G) ∉ zpowers ((x:c.H):G) ∧
      MulAut.conj g (m:G) ∉ zpowers ((y:c.H):G) := by
  let E : Subgroup c.H := zpowers (x:c.H) ⊔ zpowers (y:c.H)
  have hmap : E.map c.H.subtype = zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G) := by
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  have hE : Nat.card E=9 := by
    rw [←card_map_of_injective c.H.subtype_injective,hmap]
    exact (cubic_plane_data c x y hx hy).2
  have hi : E.index=64 := by
    have hh := E.card_mul_index
    rw [hE,H_card c] at hh
    omega
  let P : Sylow 3 c.H := (IsPGroup.of_card (p := 3) (n := 2) hE).toSylow
    (by rw [hi]; decide)
  obtain ⟨g,_,hI,_,_⟩ := exists_local_pair c (default : Sylow 2 c.H)
  let I := c.H ⊓ c.M.map (MulAut.conj g).toMonoidHom
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := I) 3 (by rw [hI]; decide)
  let uH : c.H := ⟨u,u.property.1⟩
  have huH : orderOf uH=3 := (orderOf_coe uH).symm.trans ((orderOf_coe u).trans hu)
  obtain ⟨v,hv⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using huH)
  obtain ⟨h,hh⟩ := isConj_iff.mp hv
  obtain ⟨m,hm,he⟩ := u.property.2
  have he' : MulAut.conj g m=(u:G) := he
  let mM : c.M := ⟨m,hm⟩
  have hm3 : orderOf mM=3 := by
    have ho := (MulAut.conj g).orderOf_eq m
    rw [he',orderOf_coe,hu] at ho
    exact (orderOf_coe mM).symm.trans ho.symm
  have hconj : MulAut.conj ((h:G)*g) m = ((v:c.H):G) := by
    change ((h:G)*g)*m*((h:G)*g)⁻¹=((v:c.H):G)
    calc
      _ = (h:G)*(g*m*g⁻¹)*(h:G)⁻¹ := by group
      _ = (h:G)*(u:G)*(h:G)⁻¹ := congrArg (fun w : G => (h:G)*w*(h:G)⁻¹) he
      _ = ((v:c.H):G) := congrArg Subtype.val hh
  have hvE : ((v:c.H):G) ∈ E.map c.H.subtype := mem_map_of_mem _ v.property
  have hvM : ((v:c.H):G) ∈ c.M.map (MulAut.conj ((h:G)*g)).toMonoidHom :=
    hconj ▸ mem_map_of_mem _ hm
  have hv3 : orderOf ((v:c.H):G)=3 := by
    rw [←hconj,(MulAut.conj _).orderOf_eq]
    exact (orderOf_coe mM).trans hm3
  have havoid {d : G2ThreeConfiguration G} (a : d.H₁) (ha : orderOf a=3)
      (hdM : d.M=c.M) : ((v:c.H):G) ∉ zpowers ((a:d.H):G) := by
    intro hmemb
    have heq : zpowers ((v:c.H):G)=zpowers ((a:d.H):G) :=
      eq_of_le_of_card_ge (zpowers_le.mpr hmemb) (by
        rw [Nat.card_zpowers,Nat.card_zpowers,hv3,orderOf_coe,orderOf_coe,ha])
    have hle : zpowers ((v:c.H):G) ≤ c.M.map (MulAut.conj ((h:G)*g)).toMonoidHom :=
      zpowers_le.mpr hvM
    rw [heq,←hdM] at hle
    exact cubic_factor_not_mem_conjugate_M d a ha ((h:G)*g) (hle (mem_zpowers _))
  refine ⟨mM,(h:G)*g,hm3,?_,?_,?_⟩
  · change MulAut.conj ((h:G)*g) m ∈ _
    rw [hconj,←hmap]
    exact hvE
  · change MulAut.conj ((h:G)*g) m ∉ _
    rw [hconj]
    exact havoid (d := c) x hx rfl
  · change MulAut.conj ((h:G)*g) m ∉ _
    rw [hconj]
    exact havoid (d := swapFactors c) y hy rfl


end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
