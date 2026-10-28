module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenWeakClosure
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenInvolutions.Models
public import Theory.SpecificGroups.OrthogonalFourBinary.InvertingPlane
public import Theory.Representation.InvolutionFixedPlane
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The chosen Sylow involutions and their action, original 15.2.25

In the orthogonal alternative, the marked inverter of the odd core has a
nonzero fixed vector with a cubic fixer. Uniqueness puts the lifted fixer in
Mc, but the original intersection M ∩ Mc has only a two-group image. Thus
this alternative is impossible. The surviving actual action images are S3,
D10 and Sz(2), and have cyclic Sylow two-subgroups. Their unique involution
fixes the distinguished plane, proving the involution containment. An actor
fixing that plane has all its displacements in it, giving the commutator bound.
The same cyclic Sylow action gives the two-rank bound used on the critical path.

The explicit earlier inputs are the model alternatives and fixed-plane/odd-core
marking of 15.2.13, the intersection identity of 15.2.14(5), and uniqueness
15.2.15. No involution containment, displacement bound or rank bound is assumed.
Source: Aschbacher--Smith, pp.1111--1112,1118--1120.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem cyclic_square_one {D : Type*} [Group D] [Finite D]
    (P : Subgroup D) [IsCyclic P] {b r : D} (hb : b ∈ P) (hr : r ∈ P)
    (hb2 : orderOf b = 2) (hr2 : r ^ 2 = 1) : r = 1 ∨ r = b := by
  by_cases he : r = 1
  · exact Or.inl he
  · exact Or.inr (congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨r,hr⟩ : P)) (y := (⟨b,hb⟩ : P))
      (by rw [←Subgroup.orderOf_coe]; exact orderOf_eq_prime hr2 he)
      (by rw [←Subgroup.orderOf_coe]; exact hb2)))

private theorem source_cyclic_involutions {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (b : internalActionImage M V h.prepared.normalized)
    (hb : b ∈ (T.subtype h.maximal.1.2 : Subgroup M).map
      (actionHom M V h.prepared.normalized).rangeRestrict)
    (hb2 : orderOf b = 2)
    (hcyclic : IsCyclic ((T.subtype h.maximal.1.2 : Subgroup M).map
      (actionHom M V h.prepared.normalized).rangeRestrict))
    (hfixed : ∀ v : V, (v : G) ∈ ZS ↔ b.val v = v) :
    (∀ x ∈ (T : Subgroup G), x ^ 2 = 1 →
      x ∈ (T : Subgroup G) ⊓ centralizer (ZS : Set G)) ∧
      primeRank 2 (internalActionImage M V h.prepared.normalized) ≤ 1 := by
  let f : M →* internalActionImage M V h.prepared.normalized :=
    (actionHom M V h.prepared.normalized).rangeRestrict
  let P : Sylow 2 (internalActionImage M V h.prepared.normalized) :=
    (T.subtype h.maximal.1.2).mapSurjective (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  have hPc : IsCyclic P := hcyclic
  let := hPc
  refine ⟨?_, P.primeRank_le_one_of_isCyclic hPc⟩
  intro x hx hx2
  let xM : M := ⟨x,h.maximal.1.2 hx⟩
  have hfx : f xM ∈ (P : Subgroup _) := mem_map_of_mem f hx
  have hfx2 : (f xM)^2 = 1 := by
    rw [←map_pow,show xM^2=1 from Subtype.ext hx2,map_one]
  have hcases := cyclic_square_one (P : Subgroup _) hb hfx hb2 hfx2
  refine ⟨hx,?_⟩
  intro z hz
  let v : V := ⟨z,hgeo.plane_le hz⟩
  have hv : (f xM).val v = v := by
    rcases hcases with he | he
    · rw [he]; rfl
    · rw [he]; exact (hfixed v).mp hz
  have he := congrArg (fun w : V => (w : G)) hv
  change x*z*x⁻¹=z at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem source_no_cubic_plane_fixer {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hi : M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G))
    (v : V) (hv : (v : G) ∈ ZS) (hv1 : v ≠ 1)
    (a : internalActionImage M V h.prepared.normalized)
    (ha : orderOf a = 3) (hav : a.val v = v) : False := by
  let f : M →* internalActionImage M V h.prepared.normalized :=
    (actionHom M V h.prepared.normalized).rangeRestrict
  let P : Sylow 2 (internalActionImage M V h.prepared.normalized) :=
    (T.subtype h.maximal.1.2).mapSurjective
    (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  have hle : (M ⊓ Mc).subgroupOf M ≤ (P : Subgroup _).comap f := by
    rw [hi,subgroupOf_sup (show M ⊓ centralizer (V : Set G) ≤ M from inf_le_left)
      h.maximal.1.2]
    apply sup_le
    · intro x hx
      have hxk : x ∈ (actionHom M V h.prepared.normalized).ker := by
        rw [actionHom_ker]
        exact hx.2
      have he : f x=1 := Subtype.ext (MonoidHom.mem_ker.mp hxk)
      change f x ∈ (P : Subgroup _)
      rw [he]
      exact one_mem _
    · intro x hx
      exact mem_map_of_mem f hx
  obtain ⟨g,hg⟩ := (actionHom M V h.prepared.normalized).rangeRestrict_surjective a
  change f g=a at hg
  have hgC : (g : G) ∈ centralizer ({(v : G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg (fun w : V => (w : G)) (show (f g).val v=v by rw [hg]; exact hav)
    change (g:G)*(v:G)*(g:G)⁻¹=(v:G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hvG : (v:G)≠1 := fun he => hv1 (Subtype.ext he)
  have hgMc : (g:G) ∈ Mc := by
    apply source_chosen_plane_subgroup_normalizer h hgeo hu (zpowers_le.mpr hv)
      (fun he => hvG (mem_bot.mp (he ▸ mem_zpowers (v:G))))
    apply Subgroup.centralizer_le_normalizer
    rwa [zpowers_eq_closure,centralizer_closure]
  have haP : a ∈ (P : Subgroup _) := by
    have hh : f g ∈ (P : Subgroup _) := hle ⟨g.property,hgMc⟩
    rwa [hg] at hh
  have hdiv : 3 ∣ Nat.card P := by
    have hd := orderOf_dvd_natCard (⟨a,haP⟩ : P)
    rw [←Subgroup.orderOf_coe,ha] at hd
    exact hd
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  rw [hn] at hdiv
  have hh := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) hdiv
  norm_num at hh
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem source_cyclic_commutator {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (_hgeo : ChosenPlaneGeometry h H ZS)
    (b : internalActionImage M V h.prepared.normalized)
    (hb : b ∈ (T.subtype h.maximal.1.2 : Subgroup M).map
      (actionHom M V h.prepared.normalized).rangeRestrict)
    (hb2 : orderOf b = 2)
    (hcyclic : IsCyclic ((T.subtype h.maximal.1.2 : Subgroup M).map
      (actionHom M V h.prepared.normalized).rangeRestrict))
    (hfixed : ∀ v : V, (v : G) ∈ ZS ↔ b.val v = v) :
    ⁅V,(T : Subgroup G) ⊓ centralizer (ZS : Set G)⁆ ≤ ZS := by
  let := h.prepared.elementary
  let ρ := imageRepresentation M V h.prepared.normalized
  let f : M →* internalActionImage M V h.prepared.normalized :=
    (actionHom M V h.prepared.normalized).rangeRestrict
  let P := (T.subtype h.maximal.1.2 : Subgroup M).map f
  let : IsCyclic P := hcyclic
  rw [commutator_comm]
  apply commutator_le.mpr
  intro s hs v hv
  let sM : M := ⟨s,h.maximal.1.2 hs.1⟩
  have hsP : f sM ∈ P := mem_map_of_mem f hs.1
  have hc : Commute b (f sM) := congrArg Subtype.val
    (mul_comm (⟨b,hb⟩ : P) ⟨f sM,hsP⟩)
  have hfix (w : Additive V) (hw : ρ b w=w) : ρ (f sM) w=w := by
    have hwZ : (w.toMul:G)∈ZS := (hfixed w.toMul).mpr hw
    apply Additive.toMul.injective
    apply Subtype.ext
    change s*(w.toMul:G)*s⁻¹=(w.toMul:G)
    rw [←hs.2 _ hwZ,mul_inv_cancel_right]
  let vV : Additive V := Additive.ofMul ⟨v,hv⟩
  have hh := Representation.displacement_fixed_of_commute_and_fixes ρ (hb2 ▸ pow_orderOf_eq_one b) hc hfix vV
  have hwZ := (hfixed (ρ (f sM) vV-vV).toMul).mpr hh
  rw [toMul_sub,Subgroup.coe_div,div_eq_mul_inv] at hwZ
  change (s*v*s⁻¹)*v⁻¹∈ZS at hwZ
  simpa only [commutatorElement_def] using hwZ

theorem source_chosen_not_omega {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hi : M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G))
    (b : internalActionImage M V h.prepared.normalized) (hb : orderOf b = 2)
    (hfixed : ∀ v : V, (v : G) ∈ ZS ↔ b.val v = v)
    (hc : ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),zpowers b⁆ =
      pPrimeCore 2 (internalActionImage M V h.prepared.normalized)) :
    letI := h.prepared.elementary
    ¬ Section01.SourceCases.Omega (imageRepresentation M V h.prepared.normalized) := by
  let := h.prepared.elementary
  intro ho
  obtain ⟨_,_,_,_,x,e,he⟩ := ho
  have hc' : ⁅pPrimeCore 2 OrthogonalFourBinary.omega,zpowers (e b)⁆ =
      pPrimeCore 2 OrthogonalFourBinary.omega := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) hc
    simpa only [map_commutator,pPrimeCore_map_iso,MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom] using hh
  obtain ⟨w,a,hw,hbw,ha,haw⟩ := OrthogonalFourBinary.SylowGeometry.inverting_involution_plane_has_cubic_fixer
    (e b) ((orderOf_injective e.toMonoidHom e.injective b).trans hb) hc'
  let v := (x.symm w).toMul
  have hv1 : v≠1 := by
    intro hv
    apply hw
    have hh := congrArg (fun t : V => x (Additive.ofMul t)) hv
    change x (x.symm w)=x 0 at hh
    simpa only [LinearEquiv.apply_symm_apply,map_zero] using hh
  have hfixb : b.val v=v := by
    apply Additive.ofMul.injective
    apply x.injective
    change x (imageRepresentation M V h.prepared.normalized b (x.symm w))=x (x.symm w)
    rw [he,LinearEquiv.apply_symm_apply,hbw]
  have hfixa : (e.symm a).val v=v := by
    apply Additive.ofMul.injective
    apply x.injective
    change x (imageRepresentation M V h.prepared.normalized (e.symm a) (x.symm w))=x (x.symm w)
    rw [he,LinearEquiv.apply_symm_apply,e.apply_symm_apply,haw]
  exact source_no_cubic_plane_fixer h hgeo hu hi v ((hfixed v).mpr hfixb) hv1
    (e.symm a) ((orderOf_injective e.symm.toMonoidHom e.symm.injective a).trans ha) hfixa
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open Subgroup Representation Stellmacher Theory.GroupTheory
open ChapterD ChapterD.UniqueFactor Section01
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Original 15.2.25 and its action consequences. The explicit inputs are
15.2.13(1--2), 15.2.14(5), and uniqueness 15.2.15. In particular the model
alternatives include the orthogonal case, which is excluded in the proof. -/
theorem source_chosen_involution_actions
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hgeo : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hi : M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G))
    (b : internalActionImage M V h.prepared.normalized)
    (hb : b ∈ (T.subtype h.maximal.1.2 : Subgroup M).map
      (actionHom M V h.prepared.normalized).rangeRestrict)
    (hb2 : orderOf b = 2)
    (hfixed : ∀ v : V, (v : G) ∈ ZS ↔ b.val v = v)
    (hc : ⁅pPrimeCore 2 (internalActionImage M V h.prepared.normalized),zpowers b⁆ =
      pPrimeCore 2 (internalActionImage M V h.prepared.normalized))
    (hcases : letI := h.prepared.elementary
      (SourceCases.Dihedral (imageRepresentation M V h.prepared.normalized) ∧
        SmallChosenActionModels (internalActionImage M V h.prepared.normalized)) ∨
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized)) :
    letI := h.prepared.elementary
    SourceCases.Dihedral (imageRepresentation M V h.prepared.normalized) ∧
      SmallChosenActionModels (internalActionImage M V h.prepared.normalized) ∧
      (∀ x ∈ (T : Subgroup G), x ^ 2 = 1 →
        x ∈ (T : Subgroup G) ⊓ centralizer (ZS : Set G)) ∧
      ⁅V,(T : Subgroup G) ⊓ centralizer (ZS : Set G)⁆ ≤ ZS ∧
      primeRank 2 (internalActionImage M V h.prepared.normalized) ≤ 1 := by
  let := h.prepared.elementary
  obtain ⟨hd,hm⟩ := hcases.resolve_right
    (source_chosen_not_omega h hgeo hu hi b hb2 hfixed hc)
  let P : Sylow 2 (internalActionImage M V h.prepared.normalized) :=
    (T.subtype h.maximal.1.2).mapSurjective
      (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  have hPc : IsCyclic P := hm.sylow_cyclic P
  obtain ⟨hinv,hrank⟩ := source_cyclic_involutions h hgeo b hb hb2 hPc hfixed
  exact ⟨hd,hm,hinv,source_cyclic_commutator h hgeo b hb hb2 hPc hfixed,hrank⟩

end CFSG.Quasithin.Chapter15.Section02
