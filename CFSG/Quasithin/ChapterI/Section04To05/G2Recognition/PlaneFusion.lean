module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PlaneNormalizer

/-!
# Exact fusion in the marked cubic plane

Conjugation in H on its cubic plane is equality or inversion. The action
on the two quaternion-axis triples has equal signs; on their cubic cycles,
an even permutation acts trivially and an odd permutation acts by inversion.
The quaternion kernel meets the plane trivially, so this calculation lifts
to the original factor embeddings. The original torus involution realizes
inversion on the whole plane.

When the plane is ambient Sylow, the preceding normalizer theorem and
Burnside fusion give exactly the same ambient fusion. Thus every subgroup
of the plane is weakly closed in it. The last result retains the original
M-cubic and describes precisely its conjugacy class inside this plane.
Every subgroup of the plane is torus invariant, including this actual
diagonal line. Thus torus invariance alone cannot force a factor line.
This is an obstruction to that local inference, not to the full source
theorem or to a statement with further odd-core constraints.

Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417; Fong–Wong, Nagoya
Math. J.36 (1969), §4C–D, p.164; Fong, Nagoya Math. J.39 (1970), §6B–C,
pp.75–77. This is the exceptional q=3 fusion calculation, not a proof of
I.4.5. The strict inequality in §4D and the invariant-line selection in
§6C both require q>3. The Sylow-nine and order-27-core exclusions and the
actual Atlas recognition equivalence remain to be proved.
`Chapter14PlaneFusion` applies these results to the original SourceLocalData.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition

private theorem perm_scalar : ∀ a x : Equiv.Perm (Fin 3),
    x*x*x=1 →
    (Equiv.Perm.sign a=1 → a*x*a⁻¹=x) ∧
    (Equiv.Perm.sign a≠1 → a*x*a⁻¹=x⁻¹) := by
  decide +kernel

private theorem perm_pair (a b x y : Equiv.Perm (Fin 3))
    (hs : Equiv.Perm.sign a * Equiv.Perm.sign b = 1) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    (a*x*a⁻¹=x ∧ b*y*b⁻¹=y) ∨ (a*x*a⁻¹=x⁻¹ ∧ b*y*b⁻¹=y⁻¹) := by
  obtain ⟨ha,ha'⟩ := perm_scalar a x (by simpa only [pow_succ,pow_zero,one_mul] using hx)
  obtain ⟨hb,hb'⟩ := perm_scalar b y (by simpa only [pow_succ,pow_zero,one_mul] using hy)
  by_cases h : Equiv.Perm.sign a=1
  · exact Or.inl ⟨ha h,hb (by simpa only [h,one_mul] using hs)⟩
  · exact Or.inr ⟨ha' h,hb' (fun h' => h (by simpa only [h',mul_one] using hs))⟩

private theorem wreath_scalar (w v : BinaryFourPlus.Wreath)
    (hw : w.right=1) (hs : BinaryFourPlus.factorSign w=1)
    (hv : v.right=1) (hv3 : v^3=1) : w*v*w⁻¹=v ∨ w*v*w⁻¹=v⁻¹ := by
  have hcube (i : BinaryFourPlus.C2) : (v.left i)^3=1 := by
    have h := congrArg (fun u : BinaryFourPlus.Wreath => u.left i) hv3
    simpa only [pow_succ, pow_zero, RegularWreathProduct.mul_left,
      RegularWreathProduct.mul_right, RegularWreathProduct.one_left,
      RegularWreathProduct.one_right, hv, one_mul, mul_one, inv_one, Pi.mul_apply,
      Pi.one_apply] using h
  have hi (i : BinaryFourPlus.C2) : i=1 ∨ i=BinaryFourPlus.swapIndex := by
    revert i
    decide
  obtain h|h := perm_pair (w.left 1) (w.left BinaryFourPlus.swapIndex)
    (v.left 1) (v.left BinaryFourPlus.swapIndex) hs (hcube _) (hcube _)
  · left
    apply RegularWreathProduct.ext
    · funext i
      have he : w.left i * v.left i * (w.left i)⁻¹ = v.left i := by
        rcases hi i with rfl|rfl
        · exact h.1
        · exact h.2
      simpa [hw,hv] using he
    · simp [hw,hv]
  · right
    apply RegularWreathProduct.ext
    · funext i
      have he : w.left i * v.left i * (w.left i)⁻¹ = (v.left i)⁻¹ := by
        rcases hi i with rfl|rfl
        · exact h.1
        · exact h.2
      simpa [hw,hv] using he
    · simp [hw,hv]

open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

private theorem planeH_card (x : c.H₁) (y : c.H₂) (hx : orderOf x=3) (hy : orderOf y=3) :
    Nat.card (zpowers (x:c.H) ⊔ zpowers (y:c.H) : Subgroup c.H)=9 := by
  have hmap : (zpowers (x:c.H) ⊔ zpowers (y:c.H)).map c.H.subtype =
      zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G) := by
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  have hh := (cubic_plane_data c x y hx hy).2
  rwa [←hmap,card_map_of_injective c.H.subtype_injective] at hh

private theorem planeH_faithful (x : c.H₁) (y : c.H₂) (hx : orderOf x=3) (hy : orderOf y=3) :
    Set.InjOn (coreOuterAction c) (zpowers (x:c.H) ⊔ zpowers (y:c.H) : Subgroup c.H) := by
  let E := zpowers (x:c.H) ⊔ zpowers (y:c.H)
  have hd : Disjoint E (coreOuterAction c).ker := disjoint_of_coprime_natCard (by
    rw [coreOuterAction_kernel c,quaternionCore_card c,planeH_card c x y hx hy]
    decide)
  intro a ha b hb he
  have hk : a*b⁻¹ ∈ (coreOuterAction c).ker := by
    change coreOuterAction c (a*b⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  exact mul_inv_eq_one.mp (hd.le_bot ⟨E.mul_mem ha (E.inv_mem hb),hk⟩)

private theorem planeH_scalar (x : c.H₁) (y : c.H₂) (hx : orderOf x=3) (hy : orderOf y=3)
    (a b h : c.H) (ha : a∈zpowers (x:c.H) ⊔ zpowers (y:c.H))
    (hb : b∈zpowers (x:c.H) ⊔ zpowers (y:c.H)) (he : h*a*h⁻¹=b) :
    b=a ∨ b=a⁻¹ := by
  let E := zpowers (x:c.H) ⊔ zpowers (y:c.H)
  let Eg := zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G)
  have hmap : E.map c.H.subtype=Eg := by
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    rfl
  let : IsElementaryAbelian 3 Eg := (cubic_plane_data c x y hx hy).1
  have haG : (a:G)^3=1 := elemPow_eq_one_of_isElementaryAbelian _
    (hmap ▸ mem_map_of_mem c.H.subtype ha)
  have ha3 : a^3=1 := Subtype.ext haG
  let f := coreOuterAction c
  have hf3 : (f a)^3=1 := by rw [←map_pow,ha3,map_one]
  have hfe : f h*f a*(f h)⁻¹=f b := by
    simpa only [map_mul,map_inv] using congrArg f he
  rcases wreath_scalar (f h) (f a) (coreOuterAction_preserves_factors c h)
    (coreOuterAction_sign c h) (coreOuterAction_preserves_factors c a) hf3 with hh|hh
  · exact Or.inl (planeH_faithful c x y hx hy hb ha (hfe.symm.trans hh))
  · exact Or.inr (planeH_faithful c x y hx hy hb (E.inv_mem ha)
      (hfe.symm.trans (hh.trans (map_inv f a).symm)))

namespace CubicTorus
variable {c} (t : CubicTorus c)

omit [Finite G] in
/-- The common involution inverts every element of the original cubic plane. -/
theorem plane_inverted (a : G)
    (ha : a∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) :
    MulAut.conj (t.n:G) a=a⁻¹ := by
  let X : G := ((t.x:c.H):G)
  let Y : G := ((t.y:c.H):G)
  have hc : Commute X Y := congrArg Subtype.val
    (c.commute t.x t.x.property t.y t.y.property)
  have hn : zpowers Y ≤ normalizer (zpowers X : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    apply zpowers_le.mpr
    rw [zpowers_eq_closure,centralizer_closure]
    exact mem_centralizer_singleton_iff.mpr hc.eq.symm
  change a∈(↑(zpowers X ⊔ zpowers Y):Set G) at ha
  rw [coe_mul_of_right_le_normalizer_left _ _ hn] at ha
  obtain ⟨b,hb,d,hd,rfl⟩ := ha
  obtain ⟨i,rfl⟩ := mem_zpowers_iff.mp hb
  obtain ⟨j,rfl⟩ := mem_zpowers_iff.mp hd
  have hX : MulAut.conj (t.n:G) X=X⁻¹ := congrArg Subtype.val t.invert_left
  have hY : MulAut.conj (t.n:G) Y=Y⁻¹ := congrArg Subtype.val t.invert_right
  simp only [map_mul,map_zpow,hX,hY,inv_zpow,mul_inv_rev]
  exact (hc.zpow_zpow i j).inv_inv.eq

omit [Finite G] in
/-- The common torus normalizes every subgroup of the cubic plane.
At q=3, torus invariance alone therefore does not select the factor lines. -/
theorem torus_normalizes_plane_subgroup (A : Subgroup G)
    (hA : A ≤ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) :
    t.torus.map c.H.subtype ≤ normalizer (A:Set G) := by
  rw [torus, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  apply sup_le
  · apply zpowers_le.mpr
    apply Subgroup.centralizer_le_normalizer
    intro a ha
    have hAH : A ≤ c.H := hA.trans (sup_le
      (zpowers_le.mpr t.x.val.property) (zpowers_le.mpr t.y.val.property))
    exact mem_centralizer_singleton_iff.mp (t.centralizer ▸ hAH ha)
  · apply zpowers_le.mpr
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro a ⟨b, hb, rfl⟩
      change MulAut.conj (t.n:G) b ∈ A
      rw [t.plane_inverted b (hA hb)]
      exact A.inv_mem hb
    · intro a ha
      refine ⟨a⁻¹, A.inv_mem ha, ?_⟩
      change MulAut.conj (t.n:G) a⁻¹ = a
      rw [t.plane_inverted a⁻¹ (hA (A.inv_mem ha)), inv_inv]

/-- Inside H, fusion in the original plane is exactly equality or inversion. -/
theorem plane_fusion_in_H_iff (a b : G)
    (ha : a ∈ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (hb : b ∈ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) :
    (∃ h ∈ c.H, MulAut.conj h a = b) ↔ b = a ∨ b = a⁻¹ := by
  let E := zpowers (t.x:c.H) ⊔ zpowers (t.y:c.H)
  have hmap : E.map c.H.subtype =
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  constructor
  · rintro ⟨h, hh, he⟩
    rw [← hmap] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    have hlocal : (⟨h,hh⟩ : c.H)*a*(⟨h,hh⟩ : c.H)⁻¹ = b := Subtype.ext he
    rcases planeH_scalar c t.x t.y t.x_order t.y_order a b ⟨h,hh⟩ ha hb hlocal with h|h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (rfl|rfl)
    · exact ⟨1, c.H.one_mem, by simp⟩
    · exact ⟨t.n, t.n.property, t.plane_inverted a ha⟩

/-- In the Sylow-nine branch, ambient element fusion is exactly equality or inversion. -/
theorem plane_isConj_iff_of_sylow
    (hSylow : ∃ P : Sylow 3 G, (P:Subgroup G) =
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (a b : G)
    (ha : a ∈ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (hb : b ∈ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) :
    IsConj a b ↔ b = a ∨ b = a⁻¹ := by
  constructor
  · intro h
    exact (t.plane_fusion_in_H_iff a b ha hb).mp
      (t.plane_fusion_in_H_of_sylow hSylow a b ha hb h)
  · intro h
    obtain ⟨g, _, hg⟩ := (t.plane_fusion_in_H_iff a b ha hb).mpr h
    exact isConj_iff.mpr ⟨g, hg⟩

/-- No two distinct subgroups of the cubic plane fuse in the Sylow-nine branch. -/
theorem plane_subgroup_eq_of_conjugate_of_sylow
    (hSylow : ∃ P : Sylow 3 G, (P:Subgroup G)=
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (A B : Subgroup G)
    (hA : A ≤ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (hB : B ≤ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (g : G) (he : A.map (MulAut.conj g).toMonoidHom=B) : A=B := by
  apply eq_of_le_of_card_ge
  · intro a ha
    have hb : MulAut.conj g a∈B := he ▸ mem_map_of_mem _ ha
    have hc := (t.plane_isConj_iff_of_sylow hSylow a (MulAut.conj g a)
      (hA ha) (hB hb)).mp (isConj_iff.mpr ⟨g,rfl⟩)
    rcases hc with hc|hc
    · exact hc ▸ hb
    · have hi : a⁻¹∈B := hc ▸ hb
      simpa only [inv_inv] using B.inv_mem hi
  · rw [←he,card_map_of_injective (MulAut.conj g).injective]

/-- The actual marked M supplies a diagonal whose entire ambient class in a
Sylow plane consists of that element and its inverse. The original M and
conjugating element are retained. -/
theorem exists_marked_M_plane_fusion :
    ∃ (m : c.M) (g : G),
      let E : Subgroup G := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
      let d : G := MulAut.conj g (m:G)
      orderOf m = 3 ∧ d ∈ E ∧
      d ∉ zpowers ((t.x:c.H):G) ∧ d ∉ zpowers ((t.y:c.H):G) ∧
      t.torus.map c.H.subtype ≤ normalizer (zpowers d : Set G) ∧
      ((∃ P : Sylow 3 G, (P:Subgroup G) = E) →
        ∀ a ∈ E, IsConj (m:G) a ↔ a = d ∨ a = d⁻¹) := by
  obtain ⟨m, g, hm, hd, hdx, hdy⟩ :=
    exists_marked_M_diagonal c t.x t.y t.x_order t.y_order
  refine ⟨m, g, hm, hd, hdx, hdy,
    t.torus_normalizes_plane_subgroup _ (zpowers_le.mpr hd), ?_⟩
  intro hSylow a ha
  have hmd : IsConj (m:G) (MulAut.conj g (m:G)) := isConj_iff.mpr ⟨g, rfl⟩
  exact ⟨fun h => (t.plane_isConj_iff_of_sylow hSylow _ a hd ha).mp (hmd.symm.trans h),
    fun h => hmd.trans ((t.plane_isConj_iff_of_sylow hSylow _ a hd ha).mpr h)⟩

end CubicTorus

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
