module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.NormalizerProduct.SourceControl
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.PGroupCore
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.InvolutionGeometry
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# Earlier inputs and the remaining kernel control for the swapping branch

The source uses H = G₁, K = O²(H), Q = O₂(H), and the marked
L₁ = O²(N_L(V₁)). Quotient commutator generation from 12.8.5(1), as
used in 14.4.4, places U in K by the Frattini argument below. In split
Sylow coordinates the actual A = ⟨a,[U,a]⟩ is Jₑ(T ∩ L); since T
normalizes L, it normalizes this literal A. Only the chosen a is required
to be involutory. No elementary hypothesis on the whole Wᵍ is made.

The cubic consumer uses the literal π = H → H/O₂(H) and restricts the
additional control to K ∩ π⁻¹(C(a*)). The existing genuine block argument
in LocalActions/QuaternionResidual/CoreAction gives C_H(U) ≤ C_H(A).
The remaining error is a central involution of C_H(U), so it is enough
that the relevant actors fix those involutions. This is weaker than
centralizing all of C_H(U), but is still an UNDISCHARGED extra premise.

The reduced local diagnostic H = (U × E₄) ⋊ (S₃ × S₃), |H| = 4608,
has the correct action kernel and cubic quotient decomposition, with
C_H(U) ≤ C_H(A) and N_H(A) Sylow two, but |N_H(A)* L₁*| = 12 < 36.
Its lift error is a central involution in the extra E₄ moved by the fixed
cubic. It does not construct L, Uᵍ or the standing simple QTKE ambient
arrangement, and is not a counterexample to 14.4.4. Taking the untwisted
swap in the same local group gives the product while still violating the
strong double-centralizer bound; that bound is not necessary locally.

Provenance still required in source assembly: qt-12-08 and qt-14-03-prelim
supply the genuine earlier quotient-generation and embedded block inputs;
the split-block source owner supplies the compatible Sylow coordinates.
No cited legacy chapter declaration supplies these inputs. The ambient
argument controlling the central involutions remains unresolved here.
Final normalizer-product assembly belongs to
qt-14-04-d4-quaternion-normalizer-product. Neither later U = Q nor the
split-branch contradiction is used to establish the control.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 12.8.2–5,
12.8.9–12, and the proof of 14.4.4, printed pp.1006–1007.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting.SourceControl
variable {H : Type*} [Group H] [Finite H]

/-- Apply the Frattini deduction to the actual marked residual, not an
assumed two-perfect label for L₁. The generation premise is precisely the
image of [U,L₁] in U/Z(U). -/
public theorem core_le_two_residual
    (U : Subgroup H) [U.Normal] (d : QuaternionCentralProductData U)
    (N : Subgroup H)
    (hspan : (⁅U, (pResidual 2 N).map N.subtype⁆.subgroupOf U).map
      (QuotientGroup.mk' (center U)) = ⊤) : U ≤ pResidual 2 H :=
  QuaternionSourceControl.core_le_residual U d ((pResidual 2 N).map N.subtype)
    (isPPerfect_embedded_pResidual 2 N) hspan

/-- The actual quotient-centralizing cubic admits a lift under control of
central involutions alone. The source must still discharge hcontrol. -/
public theorem marked_cubic_lift_of_central_involutions
    (U : Subgroup H) [U.Normal] (d : QuaternionCentralProductData U)
    (N : Subgroup H)
    (hspan : (⁅U, (pResidual 2 N).map N.subtype⁆.subgroupOf U).map
      (QuotientGroup.mk' (center U)) = ⊤)
    (hkernel : ((quotientAut (center U)).comp
      (MulAut.conjNormal : H →* MulAut U)).ker = pCore 2 H)
    (a : H) (ha : a ^ 2 = 1)
    (hswap : d.left.map (MulAut.conjNormal a).toMonoidHom = d.right)
    (hfix : centralizer (U : Set H) ≤ centralizer ({a} : Set H))
    (hcontrol : ∀ c ∈ pResidual 2 H ⊓
      (centralizer ({QuotientGroup.mk' (pCore 2 H) a} : Set (H ⧸ pCore 2 H))).comap
        (QuotientGroup.mk' (pCore 2 H)),
      ∀ z ∈ centralizer (U : Set H),
        z ∈ centralizer (centralizer (U : Set H) : Set H) → z ^ 2 = 1 → Commute c z)
    (k : H) (hk : k ∈ pResidual 2 H)
    (hk3 : (QuotientGroup.mk' (pCore 2 H) k) ^ 3 = 1)
    (hka : Commute (QuotientGroup.mk' (pCore 2 H) k)
      (QuotientGroup.mk' (pCore 2 H) a)) :
    ∃ c ∈ pResidual 2 H, c ^ 3 = 1 ∧ Commute c a ∧
      QuotientGroup.mk' (pCore 2 H) c = QuotientGroup.mk' (pCore 2 H) k := by
  let π := QuotientGroup.mk' (pCore 2 H)
  let J := pResidual 2 H ⊓ (centralizer ({π a} : Set (H ⧸ pCore 2 H))).comap π
  have hUJ : U ≤ J := by
    intro u hu
    refine ⟨core_le_two_residual U d N hspan hu, ?_⟩
    have huQ : u ∈ pCore 2 H := by
      rw [← hkernel]
      change quotientAut (center U) (MulAut.conjNormal u) = 1
      apply (d.quotientAut_eq_one_iff_inner _).mpr
      exact ⟨⟨u, hu⟩, MulEquiv.ext (fun _ => rfl)⟩
    change π u ∈ centralizer ({π a} : Set (H ⧸ pCore 2 H))
    rw [show π u = 1 from (QuotientGroup.eq_one_iff _).mpr huQ]
    exact (centralizer _).one_mem
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hc3, hca, he⟩ := d.cubic_centralizer_lift_of_central_involutions
    U (pCore 2 H) pCore_isPGroup hkernel J hUJ a ha hfix hcontrol hswap k
    ⟨hk, mem_centralizer_singleton_iff.mpr hka⟩ hk3 hka
  exact ⟨c, hc.1, hc3, hca, he⟩

open Matrix.PSL3Two.SplitParabolic
variable {G : Type*} [Group G]

/-- The compatible flagged Sylow model identifies the literal generated
subgroup for every chosen outside involution. -/
public theorem thompson_literal_sixteen
    (f : Unitriangular.T →* G) (hf : Function.Injective f)
    (U TL : Subgroup G) (hU : Unitriangular.U.map f = U) (hTL : f.range = TL)
    (a : G) (haTL : a ∈ TL) (ha : a ^ 2 = 1) (hout : a ∉ U) :
    Stellmacher.elementaryAbelianMaxJ TL = zpowers a ⊔ ⁅U, zpowers a⁆ := by
  have haRange : a ∈ f.range := by rwa [hTL]
  obtain ⟨x, hx⟩ := haRange
  have hx2 : x ^ 2 = 1 := hf (by rw [map_pow, hx, ha, map_one])
  have hxout : x ∉ Unitriangular.U := by
    intro hm
    exact hout (hU ▸ (hx ▸ mem_map_of_mem f hm))
  have hgen := (Unitriangular.generation_of_mem_A_outside x
    (Unitriangular.outside_involution_mem_middle x hxout hx2) hxout).symm
  rw [← hTL, MonoidHom.range_eq_map, Stellmacher.elementaryAbelianMaxJ_map_injective f hf,
    Unitriangular.thompson_eq, hgen, Subgroup.map_sup, map_commutator, MonoidHom.map_zpowers, hU, hx]

/-- Normality of T ∩ L in T supplies normalization of precisely
⟨a,[U,a]⟩, through its proved elementary Thompson description. -/
public theorem sylow_normalizes_literal_sixteen
    (f : Unitriangular.T →* G) (hf : Function.Injective f)
    (U L T : Subgroup G) (hU : Unitriangular.U.map f = U) (hTL : f.range = T ⊓ L)
    (hTLN : T ≤ normalizer (L : Set G))
    (a : G) (haTL : a ∈ T ⊓ L) (ha : a ^ 2 = 1) (hout : a ∉ U) :
    T ≤ normalizer ((zpowers a ⊔ ⁅U, zpowers a⁆ : Subgroup G) : Set G) := by
  rw [← thompson_literal_sixteen f hf U (T ⊓ L) hU hTL a haTL ha hout]
  have hN : T ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (le_inf T.le_normalizer hTLN).trans inf_normalizer_le_normalizer_inf
  intro t ht
  rw [mem_normalizer_iff_map_conj_eq]
  change (Stellmacher.elementaryAbelianMaxJ (T ⊓ L)).map
    (MulAut.conj t).toMonoidHom = _
  rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv (MulAut.conj t)]
  have htmap : (T ⊓ L).map (MulAut.conj t).toMonoidHom = T ⊓ L :=
    mem_normalizer_iff_map_conj_eq.mp (hN ht)
  rw [htmap]

end CFSG.Quasithin.Chapter14.Section04.DimensionFour.SplitImage.InvolutionSplitting.SourceControl
