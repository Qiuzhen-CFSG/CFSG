module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.SylowChoice

/-!
# Marking the adapted conjugator

R is Sylow in C_{K′}(z): that centralizer lies in the original relative
normalizer because C_G(z) ≤ H. For the conjugator chosen in 16.4.2(4),
both R and z^g lie in T^g ∩ C_{K′}(z). Sylow maximality and |R| = 2
therefore give z^g = r. Correcting g retains K′ and its component L′.

This is the element-level identification needed to transport weak closure
to the opposite center. It does not assume or prove the outer action of z
on L′.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed p.1185, the transition to symmetry. Here z^g
means left conjugation, g*z*g⁻¹.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The adapted conjugator sends the original central involution to the actual r. -/
theorem conjugate_z_eq_r (h : IntersectionSetup T z L g R)
    (hr2 : orderOf r = 2) (hR : R = zpowers r)
    (htransport : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
        (T : Subgroup G).conjBy g) : MulAut.conj g z = r := by
  let C := (centralizer (L : Set G)).conjBy g ⊓ involutionCentralizer z
  have hRC : R ≤ C := le_inf (h.sylow.le.trans inf_le_left)
    (h.le_sylow.trans h.sylow_centralizes)
  have hCH : C ≤ (centralizer (L : Set G)).conjBy g ⊓
      normalizer (centralizer (L : Set G) : Set G) := by
    rw [h.normalizers_eq]
    exact le_inf inf_le_left (inf_le_right.trans h.toStandardSetup.centralizer_z_le)
  have hRs : SylowIn R C := SylowIn.of_maximal h.sylow.isPGroup hRC
    (fun Q hp hQ hRQ => h.sylow.maximal hp (hQ.trans hCH) hRQ)
  have hRTg : R ≤ (T : Subgroup G).conjBy g :=
    (le_inf h.le_sylow ((h.sylow.le.trans inf_le_left).trans
      ((centralizer (L : Set G)).conjBy g).le_normalizer)).trans htransport
  have hzTg : z ∈ (T : Subgroup G).conjBy g :=
    htransport ⟨h.mem_sylow, h.z_normalizes_conjugate⟩
  have hcap : (T : Subgroup G).conjBy g ⊓ C = R :=
    hRs.maximal
      ((T.isPGroup'.map (MulAut.conj g).toMonoidHom).of_injective
        (inclusion inf_le_left) (inclusion_injective _))
      inf_le_right (le_inf hRTg hRC)
  have hgzC : MulAut.conj g z ∈ involutionCentralizer z := by
    obtain ⟨x, hx, hxeq⟩ := hzTg
    change MulAut.conj g x = z at hxeq
    apply mem_centralizer_singleton_iff.mpr
    have hc := congrArg (MulAut.conj g)
      (mem_centralizer_singleton_iff.mp (h.sylow_centralizes hx)).symm
    simpa only [map_mul, hxeq] using hc
  have hgzR : MulAut.conj g z ∈ R := hcap ▸
    (show MulAut.conj g z ∈ (T : Subgroup G).conjBy g ⊓ C from
      ⟨⟨z, h.mem_sylow, rfl⟩, ⟨z, h.toStandardSetup.z_mem_commutingSylow.2, rfl⟩, hgzC⟩)
  rw [hR] at hgzR
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hr2] at hgzR
  simp only [Finset.mem_image, Finset.mem_range] at hgzR
  obtain ⟨n, hn, he⟩ := hgzR
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · have hz1 : z = 1 := (MulAut.conj g).injective (by simpa using he.symm)
    have hh := h.involution
    simp [hz1] at hh
  · simpa using he.symm

/-- Correct g as in 16.4.2(4), retaining both the conjugate centralizer and
its component and marking the transported involution by r. -/
theorem exists_marked_conjugator (h : IntersectionSetup T z L g R)
    (hr2 : orderOf r = 2) (hR : R = zpowers r) :
    ∃ a : G, IntersectionSetup T z L a R ∧
      (centralizer (L : Set G)).conjBy a = (centralizer (L : Set G)).conjBy g ∧
      L.conjBy a = L.conjBy g ∧
      (T : Subgroup G) ⊓ normalizer ((centralizer (L : Set G)).conjBy a : Set G) ≤
        (T : Subgroup G).conjBy a ∧ MulAut.conj a z = r := by
  obtain ⟨a, ha, hK, htransport⟩ := h.exists_adapted_setup
  exact ⟨a, ha, hK, h.toStandardSetup.component_conjugate_eq hK, htransport,
    conjugate_z_eq_r ha hr2 hR htransport⟩

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
