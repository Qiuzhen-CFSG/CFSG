module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.Commutator.CentralDihedralSylow
public import Theory.GroupTheory.PResidual.Defs

/-!
# Restricting a central cover to a subgroup with dihedral Sylow subgroups

Suppose a central extension U → G maps onto E → G, the latter kernel has
exponent two, and every involution of the former kernel is a square there.
A perfect subgroup R of E mapping onto a group B with dihedral Sylow
2-subgroups maps injectively. Pull R back to U and take the derived subgroup.
Central Sylow transfer puts the lifted kernel in the Sylow derived subgroup;
the dihedral calculation makes its elements involutions. Taking square roots
in the central kernel of U then kills their images in E.

The preliminary lemma upgrades a p-perfect p-extension of a perfect
group to a perfect group. The final version uses the constructed universal
cover but retains its square-root hypothesis explicitly. This is the central
extension restriction argument for Aschbacher--Smith 15.3.38, printed p.1137;
the kernel property suggested by I.1.3(6), printed p.407, is a separate input.
-/

public section

open Subgroup
namespace PerfectCentralCovering

/-- A p-perfect extension of a perfect group by a p-group is perfect. -/
theorem isPerfect_of_isPPerfect_of_surjective
    {R B : Type*} [Group R] [Group B] [Group.IsPerfect B]
    {p : ℕ} [Fact p.Prime] (hR : IsPPerfect p R)
    (f : R →* B) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    Group.IsPerfect R := by
  let q : R →* R ⧸ commutator R := QuotientGroup.mk' _
  have hmap : (commutator R).map f = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  have hq : Function.Surjective (q.comp f.ker.subtype) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (commutator R) z
    obtain ⟨d, hd, hdx⟩ := mem_map.mp (show f x ∈ (commutator R).map f by rw [hmap]; trivial)
    refine ⟨⟨x * d⁻¹, by simp [MonoidHom.mem_ker, hdx]⟩, ?_⟩
    change q (x * d⁻¹) = q x
    rw [map_mul, map_inv, show q d = 1 from (QuotientGroup.eq_one_iff d).mpr hd]
    simp
  exact ⟨hR (commutator R) inferInstance (hk.of_surjective (q.comp f.ker.subtype) hq)⟩

/-- In a perfect central extension, kernel elements in a Sylow two-subgroup
have square one when its image is dihedral. No primary-kernel hypothesis is needed. -/
private theorem kernel_sylow_sq_eq_one
    {D B : Type*} [Group D] [Finite D] [Group.IsPerfect D] [Group B] [Finite B]
    (f : D →* B) (hf : Function.Surjective f) (hc : f.ker ≤ center D)
    (S : Sylow 2 D) {n : ℕ} [NeZero n]
    (e : Sylow.mapSurjective hf S ≃* DihedralGroup n)
    (x : S) (hx : (x : D) ∈ f.ker) : x ^ 2 = 1 := by
  let q := f.subgroupMap (S : Subgroup D)
  let g : S →* DihedralGroup n := e.toMonoidHom.comp q
  have hg : Function.Surjective g := e.surjective.comp (f.subgroupMap_surjective _)
  have hgc : g.ker ≤ center S := by
    intro y hy
    have hqy : q y = 1 := e.injective (hy.trans e.map_one.symm)
    have hyk : (y : D) ∈ f.ker := congrArg Subtype.val hqy
    exact mem_center_iff.mpr (fun z => Subtype.ext (mem_center_iff.mp (hc hyk) (z : D)))
  have hbound := CentralExtension.card_center_inf_commutator_le_two_of_dihedral g hg hgc
  have hxc : x ∈ center S :=
    mem_center_iff.mpr (fun z => Subtype.ext (mem_center_iff.mp (hc hx) (z : D)))
  have hxd : x ∈ commutator S := by
    have h := center_inf_commutator_inf_sylow_le_commutator S
      ⟨⟨hc hx, Group.IsPerfect.mem_commutator⟩, x.property⟩
    rw [← map_subtype_commutator] at h
    obtain ⟨y, hy, he⟩ := h
    exact (Subtype.ext he : y = x) ▸ hy
  let z : (center S ⊓ commutator S : Subgroup S) := ⟨x, hxc, hxd⟩
  have hcard : Nat.card (center S ⊓ commutator S : Subgroup S) = 1 ∨
      Nat.card (center S ⊓ commutator S : Subgroup S) = 2 := by
    have hp := Nat.card_pos (α := (center S ⊓ commutator S : Subgroup S))
    omega
  have hz : z ^ 2 = 1 := by
    rcases hcard with h | h
    · have hz1 := pow_card_eq_one' (x := z)
      rw [h, pow_one] at hz1
      simp [hz1]
    · simpa only [h] using pow_card_eq_one' (x := z)
  exact congrArg Subtype.val hz

/-- A perfect subgroup with dihedral Sylow image intersects an elementary
central two-kernel trivially, provided the extension lifts to a finite central
extension whose kernel involutions are squares in that kernel. -/
theorem injective_of_kernel_involutions_are_squares
    {U E G R B : Type*} [Group U] [Finite U] [Group E] [Group G]
    [Group R] [Finite R] [Group.IsPerfect R] [Group B] [Finite B]
    (q : U →* G) (hqc : q.ker ≤ center U)
    (c : E →* G) (hc2 : ∀ z ∈ c.ker, z ^ 2 = 1)
    (h : U →* E) (hh : Function.Surjective h) (hfac : c.comp h = q)
    (hsquare : ∀ z ∈ q.ker, z ^ 2 = 1 → ∃ w ∈ q.ker, w ^ 2 = z)
    (i : R →* E) (hi : Function.Injective i)
    (f : R →* B) (hf : Function.Surjective f)
    (j : B →* G) (hij : c.comp i = j.comp f)
    (hdihedral : ∀ S : Sylow 2 B, ∃ n : ℕ, 0 < n ∧ Nonempty (S ≃* DihedralGroup n)) :
    Function.Injective f := by
  let W : Subgroup (U × R) :=
    (h.comp (MonoidHom.fst U R)).eqLocus (i.comp (MonoidHom.snd U R))
  let a : W →* U := (MonoidHom.fst U R).comp W.subtype
  let b : W →* R := (MonoidHom.snd U R).comp W.subtype
  have hab (x : W) : h (a x) = i (b x) := x.property
  have ha : Function.Injective a := by
    intro x y he
    apply Subtype.ext
    refine Prod.ext he (hi ?_)
    change i (b x) = i (b y)
    rw [← hab, ← hab, he]
  have hb : Function.Surjective b := by
    intro r
    obtain ⟨u, hu⟩ := hh (i r)
    exact ⟨⟨(u, r), hu⟩, rfl⟩
  have hbc : b.ker ≤ center W := by
    intro x hx
    have hxq : a x ∈ q.ker := by
      rw [MonoidHom.mem_ker, ← DFunLike.congr_fun hfac (a x), MonoidHom.comp_apply,
        hab, show b x = 1 from hx, map_one, map_one]
    rw [mem_center_iff]
    intro y
    apply ha
    simpa only [map_mul] using mem_center_iff.mp (hqc hxq) (a y)
  let D := commutator W
  let : Group.IsPerfect D := commutator_isPerfect_of_surjective_of_ker_le_center b hb hbc
  let d : D →* R := b.comp D.subtype
  have hd : Function.Surjective d := by
    have hm : D.map b = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hb]
      exact Group.IsPerfect.commutator_eq_top
    intro r
    obtain ⟨w, hw, he⟩ := mem_map.mp (show r ∈ D.map b by rw [hm]; trivial)
    exact ⟨⟨w, hw⟩, he⟩
  let k : D →* U := a.comp D.subtype
  have hk : Function.Injective k := ha.comp D.subtype_injective
  have hkd (x : D) : h (k x) = i (d x) := hab x
  have hqk (x : D) : q (k x) = j (f (d x)) := by
    rw [← DFunLike.congr_fun hfac (k x), MonoidHom.comp_apply, hkd]
    exact DFunLike.congr_fun hij (d x)
  let fd : D →* B := f.comp d
  have hfd : Function.Surjective fd := hf.comp hd
  have hfdc : fd.ker ≤ center D := by
    intro x hx
    have hxq : k x ∈ q.ker := by rw [MonoidHom.mem_ker, hqk, show f (d x) = 1 from hx, map_one]
    rw [mem_center_iff]
    intro y
    apply hk
    simpa only [map_mul] using mem_center_iff.mp (hqc hxq) (k y)
  have hf2 : IsPGroup 2 f.ker := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply hi
    have hxc : i x ∈ c.ker := by
      change (c.comp i) (x : R) = 1
      rw [hij, MonoidHom.comp_apply, show f x = 1 from x.property, map_one]
    simpa using hc2 (i x) hxc
  let S : Sylow 2 D := Classical.choice Sylow.nonempty
  let T : Sylow 2 R := S.mapSurjective hd
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  have hxT : x ∈ (T : Subgroup R) := hf2.le_sylow_of_normal T hx
  obtain ⟨y, hy, hyx⟩ := mem_map.mp hxT
  have hyf : (⟨y, hy⟩ : S).val ∈ fd.ker := by
    change f (d y) = 1
    rw [hyx]
    exact hx
  obtain ⟨n, hn, ⟨e⟩⟩ := hdihedral (S.mapSurjective hfd)
  let : NeZero n := ⟨hn.ne'⟩
  have hy2 : y ^ 2 = 1 := congrArg Subtype.val (kernel_sylow_sq_eq_one fd hfd hfdc S e ⟨y, hy⟩ hyf)
  have hkyq : k y ∈ q.ker := by
    rw [MonoidHom.mem_ker, hqk, hyx, show f x = 1 from hx, map_one]
  obtain ⟨w, hw, hw2⟩ := hsquare (k y) hkyq (by rw [← map_pow, hy2, map_one])
  have hwc : h w ∈ c.ker := by
    change (c.comp h) w = 1
    rw [hfac]
    exact hw
  have hix : i x = 1 := by
    rw [← hyx, ← hkd, ← hw2, map_pow, hc2 _ hwc]
  exact hi (hix.trans i.map_one.symm)

/-- Apply the restriction theorem using the constructed finite universal cover.
Only square roots of its kernel involutions are needed, not a full multiplier
classification. -/
theorem injective_of_universal_kernel_involutions_are_squares
    {E G R B : Type*} [Group E] [Group G] [Finite G] [Group.IsPerfect G]
    [Group R] [Finite R] [Group.IsPerfect R] [Group B] [Finite B]
    (c : Cover E G) (hc2 : ∀ z ∈ c.toMonoidHom.ker, z ^ 2 = 1)
    (hsquare : ∀ z ∈ (universalProjection G).ker, z ^ 2 = 1 →
      ∃ w ∈ (universalProjection G).ker, w ^ 2 = z)
    (i : R →* E) (hi : Function.Injective i)
    (f : R →* B) (hf : Function.Surjective f)
    (j : B →* G) (hij : c.toMonoidHom.comp i = j.comp f)
    (hdihedral : ∀ S : Sylow 2 B, ∃ n : ℕ, 0 < n ∧ Nonempty (S ≃* DihedralGroup n)) :
    Function.Injective f := by
  let : Group.IsPerfect E := c.isPerfect
  obtain ⟨h, hfac, _⟩ := universalProjection_existsUnique_lift
    c.toMonoidHom c.surjective c.ker_le_center
  have hh : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect c.toMonoidHom h
      (by rw [hfac]; exact universalProjection_surjective G) c.ker_le_center
  exact injective_of_kernel_involutions_are_squares (universalProjection G)
    (universalProjection_ker_le_center G) c.toMonoidHom hc2 h hh hfac hsquare
    i hi f hf j hij hdihedral

end PerfectCentralCovering
