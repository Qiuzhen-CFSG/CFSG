module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.TransvectionSubgroups

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-!
# Lifting a full fixed-space quotient action

A faithful full action on the quotient by the common fixed space lifts every
binary transvection.  The root orbit then gives a unique centre above every
nonzero quotient point.  The centre section is additive, and its image is the
spanning root orbit; hence the common fixed space is zero and the original
subgroup is the full linear group.

Source: Aschbacher--Smith, G.3.1, printed pp.337--338 (PDF pp.348--349).
-/

@[expose] public section

open BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03.Reduced

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (BinaryLinear.GL V)} {Δ : Set V}

private theorem binary_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (binary_cases a).resolve_left ha

private theorem add_self_eq_zero {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (x : W) : x + x = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using
    congrArg (fun c : ZMod 2 => c • x) h

private theorem exists_one_zero {f g : V →ₗ[ZMod 2] ZMod 2}
    (hf : f ≠ 0) (hfg : f ≠ g) : ∃ x, f x = 1 ∧ g x = 0 := by
  by_contra! h
  have h1 (x : V) (hx : f x = 1) : g x = 1 := scalar_one (h x hx)
  obtain ⟨y, hy⟩ : ∃ y, f y = 1 := by
    obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
      by_contra hn
      exact hf (LinearMap.ext (by simpa using hn))
    exact ⟨y, scalar_one hy⟩
  apply hfg
  ext x
  rcases binary_cases (f x) with hx | hx
  · rcases binary_cases (g x) with hgx | hgx
    · exact hx.trans hgx.symm
    · have hs := h1 (x + y) (by simp [hx, hy])
      simp only [map_add, hgx, h1 y hy] at hs
      exact False.elim (by revert hs; decide)
  · exact hx.trans (h1 x hx).symm

private theorem transvection_pair {v w : V} {f g : V →ₗ[ZMod 2] ZMod 2}
    (hv : v ≠ 0) (hw : w ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfv : f v = 0) (hgw : g w = 0)
    (hprod : BinaryLinear.transvection v f hfv * BinaryLinear.transvection w g hgw = 1 ∨
      BinaryLinear.OuterCyclic.IsTransvection (BinaryLinear.transvection v f hfv * BinaryLinear.transvection w g hgw)) :
    v = w ∨ f = g := by
  by_cases hfg : f = g
  · exact Or.inr hfg
  left
  obtain ⟨x, hfx, hgx⟩ := exists_one_zero hf hfg
  obtain ⟨y, hgy, hfy⟩ := exists_one_zero hg (Ne.symm hfg)
  have hx : (BinaryLinear.transvection v f hfv * BinaryLinear.transvection w g hgw) x = x + v := by
    change (x + g x • w) + f (x + g x • w) • v = x + v
    simp [hgx, hfx]
  have hy : (BinaryLinear.transvection v f hfv * BinaryLinear.transvection w g hgw) y =
      y + (w + f w • v) := by
    change (y + g y • w) + f (y + g y • w) • v = y + (w + f w • v)
    simp [hgy, hfy, add_assoc]
  rcases hprod with hprod | hprod
  · have hz : x + v = x := by simpa [hprod] using hx.symm
    exact False.elim (hv (add_eq_left.mp hz))
  · obtain ⟨u, k, _, _, hku, he⟩ := hprod
    have hx' : v = k x • u := by
      have h := hx
      rw [he] at h
      change x + k x • u = x + v at h
      exact (add_left_cancel h).symm
    have hkx : k x = 1 := by
      apply scalar_one
      intro hz
      exact hv (by simpa [hz] using hx')
    have hvu : v = u := by simpa [hkx] using hx'
    have hy' : w + f w • v = k y • v := by
      have h := hy
      rw [he] at h
      change y + k y • u = y + (w + f w • v) at h
      rw [← hvu] at h
      exact (add_left_cancel h).symm
    have hwv : w = (k y - f w) • v := by
      rw [sub_smul]
      exact eq_sub_iff_add_eq.mpr hy'
    rcases binary_cases (k y - f w) with hz | ho
    · exact False.elim (hw (by simpa [hz] using hwv))
    · simpa [ho] using hwv.symm

private theorem transvection_pair_of_mem (H : Subgroup (BinaryLinear.GL V))
    (hH : ∀ t ∈ H, t ≠ 1 → BinaryLinear.OuterCyclic.IsTransvection t)
    {v w : V} {f g : V →ₗ[ZMod 2] ZMod 2}
    (hv : v ≠ 0) (hw : w ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfv : f v = 0) (hgw : g w = 0)
    (hs : BinaryLinear.transvection v f hfv ∈ H)
    (ht : BinaryLinear.transvection w g hgw ∈ H) :
    v = w ∨ f = g := by
  apply transvection_pair hv hw hf hg hfv hgw
  by_cases he : BinaryLinear.transvection v f hfv * BinaryLinear.transvection w g hgw = 1
  · exact Or.inl he
  · exact Or.inr (hH _ (H.mul_mem hs ht) he)

private theorem common_center_of_transvections
    (H : Subgroup (BinaryLinear.GL V)) (hH : ∀ t ∈ H, t ≠ 1 → BinaryLinear.OuterCyclic.IsTransvection t)
    {x : V} {f g : V →ₗ[ZMod 2] ZMod 2}
    (hx : x ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) (hfx : f x = 0) (hgx : g x = 0)
    (hfg : f ≠ g) (hs : BinaryLinear.transvection x f hfx ∈ H)
    (hts : BinaryLinear.transvection x g hgx ∈ H) :
    ∀ t ∈ H, t ≠ 1 → ∃ k : V →ₗ[ZMod 2] ZMod 2, k ≠ 0 ∧ ∃ hkx : k x = 0,
      t = BinaryLinear.transvection x k hkx := by
  intro t ht ht1
  obtain ⟨y, k, hy, hk, hky, rfl⟩ := hH t ht ht1
  have h1 := transvection_pair_of_mem H hH hx hy hf hk hfx hky hs ht
  have h2 := transvection_pair_of_mem H hH hx hy hg hk hgx hky hts ht
  have hxy : x = y := by
    rcases h1 with hxy | hfk
    · exact hxy
    rcases h2 with hxy | hgk
    · exact hxy
    exact False.elim (hfg (hfk.trans hgk.symm))
  subst y
  exact ⟨k, hk, ⟨hky, rfl⟩⟩

private theorem root_is_transvection {H : Subgroup (BinaryLinear.GL V)} {x : V} (hx : x ≠ 0)
    {a : BinaryLinear.GL V} (ha : a ∈ rootGroup H x) (ha1 : a ≠ 1) : BinaryLinear.OuterCyclic.IsTransvection a := by
  obtain ⟨haG, f, hfx, rfl⟩ := (mem_rootGroup_iff hx).mp ha
  have hf : f ≠ 0 := by
    intro hf
    apply ha1
    ext v
    simp [BinaryLinear.transvection, hf]
  exact ⟨x, f, hx, hf, hfx, rfl⟩

end CFSG.Quasithin.ChapterG.Section03.Reduced

namespace CFSG.Quasithin.ChapterG.Section03.Reduced

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (BinaryLinear.GL V)} {Δ : Set V}

/-- A faithful surjective fixed-space quotient action lifts to the full linear group. -/
theorem eq_top_of_full_fixedQuotient [Finite G] (r : RootGeneratedOrbit G Δ)
    (hfaith : Function.Injective (fixedQuotientAction G))
    (hfull : Function.Surjective (fixedQuotientAction G)) : G = ⊤ := by
  classical
  let C := fixedSpace G
  let Q := V ⧸ C
  let q : V →ₗ[ZMod 2] Q := C.mkQ
  let ρ : G →* BinaryLinear.GL Q := fixedQuotientAction G
  have hCtop : C ≠ ⊤ := fixedSpace_ne_top r.ne_bot
  letI : FiniteDimensional (ZMod 2) V := r.finiteDimensional
  letI : Module.Finite (ZMod 2) Q := Module.Finite.quotient (ZMod 2) C
  letI : Finite Q := Module.finite_of_finite (ZMod 2)
  have hq_surj : Function.Surjective q := Submodule.Quotient.mk_surjective C
  have hq_apply (v : V) : q v = C.mkQ v := rfl
  have hρrange : ρ.range = ⊤ := MonoidHom.range_eq_top.mpr hfull
  have hq_nonzero (x : V) (hx : x ∈ Δ) : q x ≠ 0 := by
    intro hz
    apply r.center_not_mem C
      (G.le_normalizer.trans (normalizer_le_parabolic_fixedSpace G)) hCtop hx
    exact (Submodule.Quotient.mk_eq_zero C).mp hz
  have rQ : RootGeneratedOrbit ρ.range (q '' Δ) := by
    apply r.map q hq_surj ρ hfaith
      (fun g v => by rfl)
    exact hq_nonzero
  have rQtop : RootGeneratedOrbit (⊤ : Subgroup (BinaryLinear.GL Q)) (q '' Δ) := by
    simpa [hρrange] using rQ
  have hQfd : FiniteDimensional (ZMod 2) Q := inferInstance
  have hQnonzero : ∃ z : Q, z ≠ 0 := by
    obtain ⟨z, hz⟩ := rQtop.nonempty
    exact ⟨z, rQtop.nonzero z hz⟩
  have hρfaith : Function.Injective ρ := by
    simpa [ρ] using hfaith
  have lift_transvection : ∀ t : BinaryLinear.GL Q,
      BinaryLinear.OuterCyclic.IsTransvection t →
      ∃ g : G, ρ g = t ∧ BinaryLinear.OuterCyclic.IsTransvection (g.val) := by
    intro t ht
    obtain ⟨x, hx⟩ := r.nonempty
    letI : Fintype (rootGroup G x) := Fintype.ofFinite _
    have hcard : 1 < Nat.card (rootGroup G x) := by
      have := r.large_roots x hx
      omega
    have ha : ∃ a : rootGroup G x, a ≠ 1 := by
      by_contra hn
      push Not at hn
      have hall : ∀ a : rootGroup G x, a = 1 := by
        intro a
        exact hn a
      have hc : Fintype.card (rootGroup G x) ≤ 1 :=
        Fintype.card_le_one_iff.mpr (fun a b => (hall a).trans (hall b).symm)
      rw [← Nat.card_eq_fintype_card] at hc
      omega
    obtain ⟨a, ha1⟩ := ha
    let aG : G := ⟨a.val, (rootGroup_le G x) a.property⟩
    have hax : ρ aG ∈ rootGroup ρ.range (q x) := by
      apply root_mem_of_equivariant q hq_surj ρ
      · intro g v
        rfl
      · exact a.property
    have hqa : q x ≠ 0 := hq_nonzero x hx
    have hρa1 : ρ aG ≠ 1 := by
      intro he
      have he' := hρfaith (he.trans (map_one ρ).symm)
      have hv : a.val = 1 := congrArg Subtype.val he'
      exact ha1 (Subtype.ext hv)
    have hta : BinaryLinear.OuterCyclic.IsTransvection (ρ aG) :=
      root_is_transvection hqa hax hρa1
    obtain ⟨e, he⟩ := BinaryLinear.OuterCyclic.transvections_conjugate hta ht
    obtain ⟨b, hb⟩ := hfull e
    have hconj : ρ (b * aG * b⁻¹) = t := by
      calc
        ρ (b * aG * b⁻¹) = ρ b * ρ aG * (ρ b)⁻¹ := by simp [map_mul]
        _ = e * ρ aG * e⁻¹ := by rw [hb]
        _ = (MulAut.conj e) (ρ aG) := rfl
        _ = t := he
    refine ⟨b * aG * b⁻¹, hconj, ?_⟩
    have haVal : a.val ≠ 1 := by
      intro hz
      exact ha1 (Subtype.ext hz)
    obtain ⟨wa, fa, hwa, hfa, hfwa, haeq⟩ :=
      root_is_transvection (r.nonzero x hx) a.property haVal
    let hnew : (fa.comp b.val.symm.toLinearMap) (b.val wa) = 0 := by
      simp [LinearMap.comp_apply, hfwa]
    refine ⟨b.val wa, fa.comp b.val.symm.toLinearMap, ?_, ?_, ?_⟩
    · intro hz
      apply hwa
      exact b.val.injective (by simpa [hz])
    · intro hz
      apply hfa
      ext z
      have hz' := congrArg (fun F : V →ₗ[ZMod 2] ZMod 2 => F (b.val z)) hz
      simpa [LinearMap.comp_apply] using hz'
    · refine ⟨hnew, ?_⟩
      change b.val * a.val * b.val⁻¹ = BinaryLinear.transvection
          (b.val wa) (fa.comp b.val.symm.toLinearMap) hnew
      ext z
      simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
      change b.val (a.val (b.val.symm z)) =
        z + fa (b.val.symm z) • b.val wa
      rw [haeq]
      simp [BinaryLinear.transvection]
  let P : Q → Subgroup (BinaryLinear.GL V) := fun z =>
    (Subgroup.comap ρ (rootGroup (⊤ : Subgroup (BinaryLinear.GL Q)) z)).map G.subtype
  have all_trans (z : Q) (hz : z ≠ 0) :
      ∀ t : P z, t ≠ 1 → BinaryLinear.OuterCyclic.IsTransvection t.val := by
    intro t ht
    obtain ⟨u, hu, hut⟩ := t.property
    have hu1 : u ≠ 1 := by
      intro he
      apply ht
      apply Subtype.ext
      simpa [he] using hut.symm
    have htz : ρ u ∈ rootGroup (⊤ : Subgroup (BinaryLinear.GL Q)) z :=
      (Subgroup.mem_comap.mp hu)
    have htz1 : ρ u ≠ 1 := by
      intro he
      apply hu1
      exact hρfaith (he.trans (map_one ρ).symm)
    obtain ⟨w, hw, hwt⟩ := lift_transvection (ρ u)
      (root_is_transvection hz htz htz1)
    have hwu : w = u := hρfaith hw
    have hwt' : w.val = t.val := hwu ▸ hut
    rw [← hwt']
    exact hwt
  have two_root_forms (x : V) (hx : x ∈ Δ) :
      ∃ f g : V →ₗ[ZMod 2] ZMod 2,
        f ≠ 0 ∧ g ≠ 0 ∧ f x = 0 ∧ g x = 0 ∧ f ≠ g ∧
          (∃ hfx : f x = 0, BinaryLinear.transvection x f hfx ∈ rootGroup G x) ∧
          (∃ hgx : g x = 0, BinaryLinear.transvection x g hgx ∈ rootGroup G x) := by
    letI : Fintype (rootGroup G x) := Fintype.ofFinite _
    have hc : 2 < (Finset.univ : Finset (rootGroup G x)).card := by
      simpa [Nat.card_eq_fintype_card] using r.large_roots x hx
    obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ :=
      (Finset.two_lt_card.mp hc)
    have haU : a ∈ (Finset.univ : Finset (rootGroup G x)) := by simp
    have hbU : b ∈ (Finset.univ : Finset (rootGroup G x)) := by simp
    have hcU : c ∈ (Finset.univ : Finset (rootGroup G x)) := by simp
    have hp : ∃ u v : rootGroup G x, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
      by_cases ha1 : a = 1
      · have hb1 : b ≠ 1 := by intro h; exact hab (ha1.trans h.symm)
        have hc1 : c ≠ 1 := by intro h; exact hac (ha1.trans h.symm)
        exact ⟨b, c, hb1, hc1, hbc⟩
      · by_cases hb1 : b = 1
        · have hc1 : c ≠ 1 := by intro h; exact hbc (hb1.trans h.symm)
          exact ⟨a, c, ha1, hc1, hac⟩
        · exact ⟨a, b, ha1, hb1, hab⟩
    obtain ⟨u, v, hu1, hv1, huv⟩ := hp
    obtain ⟨_, f, hfx, huf⟩ := (mem_rootGroup_iff (r.nonzero x hx)).mp u.property
    obtain ⟨_, g, hgx, hvg⟩ := (mem_rootGroup_iff (r.nonzero x hx)).mp v.property
    have hf : f ≠ 0 := by
      intro hf
      apply hu1
      apply Subtype.ext
      rw [huf]
      ext z
      simp [BinaryLinear.transvection, hf]
    have hg : g ≠ 0 := by
      intro hg
      apply hv1
      apply Subtype.ext
      rw [hvg]
      ext z
      simp [BinaryLinear.transvection, hg]
    have hfg : f ≠ g := by
      intro hfg
      apply huv
      apply Subtype.ext
      calc
        (u : BinaryLinear.GL V) = BinaryLinear.transvection x f hfx := huf
        _ = BinaryLinear.transvection x g hgx := by subst g; rfl
        _ = (v : BinaryLinear.GL V) := hvg.symm
    refine ⟨f, g, hf, hg, hfx, hgx, hfg, ?_, ?_⟩
    · exact ⟨hfx, by rw [← huf]; exact u.property⟩
    · exact ⟨hgx, by rw [← hvg]; exact v.property⟩
  obtain ⟨x₀, hx₀orbit⟩ := rQtop.orbit
  have hx₀ : x₀ ∈ q '' Δ := hx₀orbit ▸ MulAction.mem_orbit_self x₀
  have hx₀nz : x₀ ≠ 0 := rQtop.nonzero x₀ hx₀
  have all_nonzero_mem : ∀ z : Q, z ≠ 0 → z ∈ q '' Δ := by
    intro z hz
    obtain ⟨e, he⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hx₀nz hz
    rw [hx₀orbit]
    exact MulAction.mem_orbit_iff.mpr ⟨⟨e, Subgroup.mem_top e⟩, he⟩
  have common_center_for (x : V) (hx : x ∈ Δ) :
      ∀ a : P (q x), a ≠ 1 →
        ∃ k : V →ₗ[ZMod 2] ZMod 2, k ≠ 0 ∧ ∃ hkx : k x = 0,
          a.val = BinaryLinear.transvection x k hkx := by
    obtain ⟨f, g, hf, hg, hfx, hgx, hfg, hmf, hmg⟩ := two_root_forms x hx
    obtain ⟨hfx', hmf'⟩ := hmf
    obtain ⟨hgx', hmg'⟩ := hmg
    have hPmem (hmem : BinaryLinear.transvection x f hfx' ∈ rootGroup G x) :
        (BinaryLinear.transvection x f hfx' : BinaryLinear.GL V) ∈ P (q x) := by
      apply (Subgroup.mem_map).mpr
      refine ⟨⟨BinaryLinear.transvection x f hfx', rootGroup_le G x hmem⟩, ?_, rfl⟩
      apply Subgroup.mem_comap.mpr
      simpa [hρrange] using
        (root_mem_of_equivariant q hq_surj ρ (fun g v => rfl) hmem)
    have hPmem' (hmem : BinaryLinear.transvection x g hgx' ∈ rootGroup G x) :
        (BinaryLinear.transvection x g hgx' : BinaryLinear.GL V) ∈ P (q x) := by
      apply (Subgroup.mem_map).mpr
      refine ⟨⟨BinaryLinear.transvection x g hgx', rootGroup_le G x hmem⟩, ?_, rfl⟩
      apply Subgroup.mem_comap.mpr
      simpa [hρrange] using
        (root_mem_of_equivariant q hq_surj ρ (fun g v => rfl) hmem)
    have hH : ∀ t : P (q x), t ≠ 1 → BinaryLinear.OuterCyclic.IsTransvection t.val :=
      all_trans (q x) (hq_nonzero x hx)
    intro a ha
    have hH' : ∀ t ∈ P (q x), t ≠ 1 →
        BinaryLinear.OuterCyclic.IsTransvection t := by
      intro t ht ht1
      have ht1' : (⟨t, ht⟩ : P (q x)) ≠ 1 := by
        intro he
        exact ht1 (congrArg Subtype.val he)
      exact all_trans (q x) (hq_nonzero x hx) ⟨t, ht⟩ ht1'
    have haVal : a.val ≠ 1 := by
      intro he
      exact ha (Subtype.ext he)
    obtain ⟨k, hk, hkx, heq⟩ := common_center_of_transvections
      (P (q x)) hH' (r.nonzero x hx) hf hg hfx hgx hfg
      (hPmem hmf') (hPmem' hmg') a.val a.property haVal
    exact ⟨k, hk, hkx, heq⟩
  have center_fiber (z : Q) (hz : z ≠ 0) :
      ∃! x : V, x ∈ Δ ∧ q x = z := by
    obtain ⟨x, hx, hqz⟩ := all_nonzero_mem z hz
    have hex : ∃ x : V, x ∈ Δ ∧ q x = z := ⟨x, hx, hqz⟩
    refine ⟨x, ⟨hx, hqz⟩, ?_⟩
    intro y hy
    have hq_y : q y = q x := hy.2.trans hqz.symm
    have hP_y : ∃ a : rootGroup G y, a ≠ 1 := by
      letI : Fintype (rootGroup G y) := Fintype.ofFinite _
      have hc := r.large_roots y hy.1
      by_contra hn
      push Not at hn
      have hall : ∀ a : rootGroup G y, a = 1 := fun a => hn a
      have hc' : Fintype.card (rootGroup G y) ≤ 1 :=
        Fintype.card_le_one_iff.mpr (fun a b => (hall a).trans (hall b).symm)
      rw [← Nat.card_eq_fintype_card] at hc'
      omega
    obtain ⟨a, ha1⟩ := hP_y
    let aG : G := ⟨a.val, (rootGroup_le G y) a.property⟩
    have haP : (aG : BinaryLinear.GL V) ∈ P (q x) := by
      apply (Subgroup.mem_map).mpr
      refine ⟨aG, ?_, rfl⟩
      apply Subgroup.mem_comap.mpr
      simpa [hρrange, hq_y] using
        (root_mem_of_equivariant q hq_surj ρ (fun g v => rfl) a.property)
    let aP : P (q x) := ⟨aG.val, haP⟩
    have haP1 : aP ≠ 1 := by
      intro he
      have hv : a.val = 1 := by
        simpa [aP, aG] using congrArg Subtype.val he
      exact ha1 (Subtype.ext hv)
    obtain ⟨k, hk, hky, haeq⟩ := common_center_for x hx aP haP1
    have haX : a.val ∈ rootGroup G x := by
      have hrad : a.val ∈ BinaryLinear.radical (centerLine x) := by
        rw [haeq]
        exact BinaryLinear.transvection_mem
          (Submodule.mem_span_singleton_self x)
          (Submodule.span_le.mpr (by simpa using hky))
      exact ⟨aG.property, hrad⟩
    by_contra hxy
    have hxy' : x ≠ y := by intro h; exact hxy h.symm
    have haeq1 : a.val = 1 :=
      (rootGroup_disjoint G hxy').le_bot ⟨haX, a.property⟩
    exact ha1 (Subtype.ext haeq1)
  let s : Q → V := fun z => if hz : z = 0 then 0 else
    Classical.choose (center_fiber z hz)
  have s_zero : s 0 = 0 := by simp [s]
  have s_spec (z : Q) (hz : z ≠ 0) : s z ∈ Δ ∧ q (s z) = z := by
    simp only [s, dif_neg hz]
    exact (Classical.choose_spec (center_fiber z hz)).1
  have s_center (x : V) (hx : x ∈ Δ) : s (q x) = x := by
    have hqx := hq_nonzero x hx
    exact (center_fiber (q x) hqx).unique (s_spec (q x) hqx) ⟨hx, rfl⟩
  have s_add_nonzero (z w : Q) (hz : z ≠ 0) (hw : w ≠ 0)
      (hzw : z + w ≠ 0) : s (z + w) = s z + s w := by
    have hne : w ∉ centerLine z := by
      intro h
      rcases (mem_centerLine_iff z w).mp h with h | h
      · exact hw h
      · subst w
        exact hzw (add_self_eq_zero z)
    obtain ⟨f, hfw, hfker⟩ := (centerLine z).exists_le_ker_of_notMem hne
    have hfz : f z = 0 := hfker (Submodule.mem_span_singleton_self z)
    have hfone : f w = 1 := scalar_one hfw
    let T := BinaryLinear.transvection z f hfz
    have hTroot : T ∈ rootGroup (⊤ : Subgroup (BinaryLinear.GL Q)) z := by
      exact ⟨Subgroup.mem_top T, BinaryLinear.transvection_mem
        (Submodule.mem_span_singleton_self z) hfker⟩
    obtain ⟨g, hg⟩ := hfull T
    have hgP : (g : BinaryLinear.GL V) ∈ P z := by
      apply (Subgroup.mem_map).mpr
      refine ⟨g, ?_, rfl⟩
      apply Subgroup.mem_comap.mpr
      simpa [hρrange] using hg ▸ hTroot
    have hg1 : g.val ≠ 1 := by
      intro he
      have hT1 : T = 1 := by
        calc
          T = ρ g := hg.symm
          _ = ρ (1 : G) := by rw [show g = 1 by exact Subtype.ext he]
          _ = 1 := map_one ρ
      have hzero := congrArg (fun e : BinaryLinear.GL Q => e w) hT1
      have hzero' : w + z = w := by
        simpa [T, BinaryLinear.transvection, hfone] using hzero
      exact hz (add_eq_left.mp hzero')
    let gP : P z := ⟨g.val, hgP⟩
    have hxg : s z ∈ Δ := (s_spec z hz).1
    have hqxg : q (s z) = z := (s_spec z hz).2
    let gP' : P (q (s z)) := ⟨g.val, by simpa [hqxg] using hgP⟩
    obtain ⟨k, hk, hkx, hgk⟩ := common_center_for (s z) hxg gP' (by
      intro he
      exact hg1 (congrArg Subtype.val he))
    have hgk' : g.val = BinaryLinear.transvection (s z) k hkx := by
      simpa [gP'] using hgk
    have hqg_sw : q (g.val (s w)) = w + z := by
      have hh := congrArg (fun e : BinaryLinear.GL Q => e (q (s w))) hg
      rw [fixedQuotientAction_apply_mkQ] at hh
      change q (g.val (s w)) = T (q (s w)) at hh
      rw [s_spec w hw |>.2] at hh
      simpa [T, BinaryLinear.transvection, hfone, hq_apply] using hh
    have hksw : k (s w) = 1 := by
      have hcases : k (s w) = 0 ∨ k (s w) = 1 := binary_cases _
      rcases hcases with h0 | h1
      · have hh := hqg_sw
        rw [hgk'] at hh
        change q (s w + k (s w) • s z) = w + z at hh
        rw [h0, zero_smul, add_zero, s_spec w hw |>.2] at hh
        apply False.elim
        apply hz
        apply add_left_cancel (a := w)
        simpa using hh.symm
      · exact h1
    have hg_sw : g.val (s w) = s w + s z := by
      rw [hgk']
      change s w + k (s w) • s z = s w + s z
      rw [hksw, one_smul]
    have hmemΔ : g.val (s w) ∈ Δ := by
      obtain ⟨x₀, hx₀⟩ := r.orbit
      rw [hx₀] at ⊢
      obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp (by
        rw [← hx₀]
        exact (s_spec w hw).1)
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨g * a, ?_⟩
      change g.val (a.val x₀) = g.val (s w)
      exact congrArg g.val ha
    have hqsum : q (s w + s z) = z + w := by
      rw [map_add, s_spec w hw |>.2, s_spec z hz |>.2, add_comm]
    have hcand : g.val (s w) ∈ Δ ∧ q (g.val (s w)) = z + w := by
      exact ⟨hmemΔ, by rw [hg_sw]; exact hqsum⟩
    have huniq : s (z + w) = g.val (s w) :=
      (center_fiber (z + w) hzw).unique (s_spec (z + w) hzw) hcand
    rw [huniq, hg_sw]
    exact add_comm _ _
  have s_add (z w : Q) : s (z + w) = s z + s w := by
    by_cases hz : z = 0
    · simp [hz, s_zero]
    by_cases hw : w = 0
    · simp [hw, s_zero]
    by_cases hzw : z + w = 0
    · have : z = w := by
        apply add_left_cancel (a := z)
        rw [hzw, add_self_eq_zero]
      subst w
      rw [add_self_eq_zero, s_zero, add_self_eq_zero]
    exact s_add_nonzero z w hz hw hzw
  let sLin : Q →ₗ[ZMod 2] V :=
    { toFun := s
      map_add' := s_add
      map_smul' := by
        intro a v
        rcases binary_cases a with rfl | rfl
        · simpa [zero_smul, s_zero]
        · simp }
  have hq_s (z : Q) : q (sLin z) = z := by
    by_cases hz : z = 0
    · simp [sLin, hz, s_zero]
    · exact s_spec z hz |>.2
  have hspan : Submodule.span (ZMod 2) (Set.range sLin) = ⊤ := by
    apply top_unique
    rw [← r.span_eq_top]
    apply Submodule.span_le.mpr
    intro x hx
    have hqx := hq_nonzero x hx
    exact Submodule.subset_span ⟨q x, by simpa [sLin] using s_center x hx⟩
  have hs_surj : Function.Surjective sLin := by
    have hrange : LinearMap.range sLin = ⊤ := by
      apply top_unique
      rw [← hspan]
      exact Submodule.span_le.mpr (by
        intro x hx
        rcases hx with ⟨z, rfl⟩
        exact ⟨z, rfl⟩)
    exact LinearMap.range_eq_top.mp hrange
  have hCbot : C = ⊥ := by
    apply (Submodule.eq_bot_iff C).mpr
    intro v hv
    have hqv : q v = 0 := (Submodule.Quotient.mk_eq_zero C).mpr hv
    obtain ⟨z, hz⟩ := hs_surj v
    have hz0 : z = 0 := by
      calc
        z = q (sLin z) := (hq_s z).symm
        _ = q v := by rw [hz]
        _ = 0 := hqv
    have hv' : v = sLin 0 := by
      rw [hz0] at hz
      exact hz.symm
    simpa [sLin, s_zero] using hv'
  have qbij : Function.Bijective q := by
    refine ⟨?_, hq_surj⟩
    intro v w h
    have hqvw : q (v - w) = 0 := by rw [map_sub, h, sub_self]
    have hv : v - w ∈ C := (Submodule.Quotient.mk_eq_zero C).mp hqvw
    have hwv : v - w = 0 := by
      rw [hCbot, Submodule.mem_bot] at hv
      exact hv
    exact sub_eq_zero.mp hwv
  let eQ : V ≃ₗ[ZMod 2] Q := LinearEquiv.ofBijective q qbij
  apply top_unique
  intro e he
  let t : BinaryLinear.GL Q := eQ.symm.trans (e.trans eQ)
  obtain ⟨g, hg⟩ := hfull t
  have hge : g.val = e := by
    ext v
    apply eQ.injective
    have hh := congrArg (fun a : BinaryLinear.GL Q => a (q v)) hg
    rw [fixedQuotientAction_apply_mkQ] at hh
    change q (g.val v) = t (q v) at hh
    have hte : t (q v) = q (e v) := by
      dsimp [t]
      have hqv' : q v = eQ v := rfl
      rw [hqv', eQ.symm_apply_apply]
      rfl
    rw [hte] at hh
    exact hh
  exact hge ▸ g.property

end CFSG.Quasithin.ChapterG.Section03.Reduced

end
