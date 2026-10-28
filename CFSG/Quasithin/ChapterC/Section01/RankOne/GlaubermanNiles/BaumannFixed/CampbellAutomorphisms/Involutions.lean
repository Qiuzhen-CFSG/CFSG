module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.Preparation
public import Theory.GroupTheory.CrossNormalInvolutions
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellComparison.Source


/-!
# The involution argument on the transported Campbell spans

For W and its inverse automorphism image W′, transport conjugation by u
on W through the actual equivalence W′≃W. The resulting marked map fixes
Φ(W′): its image in Φ(W) lies in the supplied central layer. A common
Frattini element therefore lies in V and centralizes J(H), hence is central
in H because J(H)O₂(H)=H and O₂(H) centralizes V.

The crossed-involution word calculation produces a nontrivial common
Frattini displacement whenever h and hᵍ fail to commute. Its transported
actor lies in the actual natural V, so fixed-point lifting makes that
displacement trivial, a contradiction. The theorem retains the precise
span equivalence, original u and the two actual Frattini containments;
constructing these from the Sylow automorphism remains with the automorphism
source assembly. No dihedral classification input is used.
Source: Campbell, *Pushing up in Finite Groups* (1979), II.6.2,
printed pp.29–30; the Frattini bounds are supplied by Preparation.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

private theorem private_involution_consumer (hL : InLocalClass e) (hB : IsBaumannFixed B)
    (W W' : Subgroup H) (hW : IsPGroup 2 W) (hW' : IsPGroup 2 W')
    (f : W' →* H) (hf : Function.Injective f)
    (hPhi : ∀ z : W', (z : H) ∈ (frattini W).map W.subtype →
      z ∈ frattini W' → f z ∈ center H)
    (g : W') (h : H) (hg2 : g^2=1) (hh2 : h^2=1) (hh : h ∈ W)
    (hgN : (g : H) ∈ normalizer (W : Set H)) (hhN : h ∈ normalizer (W' : Set H))
    (hfg : f g ∈ Campbell.V H) : ⁅h,(g:H)*h*(g:H)⁻¹⁆=1 := by
  by_contra hne
  obtain ⟨y,hy,hysq,hcomm,hphi,hphi'⟩ := exists_cross_frattini_displacement_of_noncommuting_involutions
    W W' hW hW' (g:H) h (congrArg Subtype.val hg2) hh2 g.property hh hgN hhN hne
  let y' : W' := ⟨y,hy.2⟩
  have hphiy : y'^2 ∈ frattini W' := by
    obtain ⟨z,hz,he⟩ := hphi'
    have he' : z=y'^2 := Subtype.ext he
    exact he' ▸ hz
  have hcent : ⁅f y',f g⁆ ∈ center H := by
    rw [←map_commutatorElement]
    have hh : ⁅y',g⁆=y'^2 := Subtype.ext hcomm
    rw [hh]
    exact hPhi (y'^2) hphi hphiy
  have hzero := hL.central_campbell_displacement_eq_one hB (f y') (f g) hfg hcent
  have hyzero : y'^2=1 := hf (by
    have hh : ⁅y',g⁆=y'^2 := Subtype.ext hcomm
    rw [←hh,map_commutatorElement,hzero,map_one])
  exact hysq (congrArg Subtype.val hyzero)

theorem InLocalClass.global_thompson_sup_core_eq_top (h : InLocalClass e) (hB : IsBaumannFixed B) :
    Campbell.J (⊤ : Subgroup H) ⊔ pCore 2 H = ⊤ := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  have hK : (Campbell.J (⊤ : Subgroup H)).Normal := by
    change (elementaryAbelianMaxJ (⊤ : Subgroup H)).Normal
    let : (elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic := elementaryAbelianMaxJ_top_characteristic
    infer_instance
  have hN : (Campbell.J (⊤ : Subgroup H) ⊔ pCore 2 H).Normal := inferInstance
  have hSN : (d.sylow : Subgroup H) ≤ Campbell.J (⊤ : Subgroup H) ⊔ pCore 2 H := by
    rw [←h.thompson_sup_core_eq_sylow hB m d hS]
    exact sup_le_sup (elementaryAbelianMaxJ_sylow_le_top d.sylow) le_rfl
  obtain ⟨g,_,hgen⟩ := h.exists_two_sylow_generators hB m d hS
  have hSgN : (d.sylow : Subgroup H).map (MulAut.conj g).toMonoidHom ≤
      Campbell.J (⊤ : Subgroup H) ⊔ pCore 2 H := by
    rintro x ⟨s,hs,rfl⟩
    exact hN.conj_mem s (hSN hs) g
  exact top_unique (hgen.symm.le.trans (sup_le hSN hSgN))

theorem InLocalClass.campbell_centralizer_global_thompson_le_center (h : InLocalClass e) (hB : IsBaumannFixed B) :
    Campbell.V H ⊓ centralizer (Campbell.J (⊤ : Subgroup H) : Set H) ≤ center H := by
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  have hVC : Campbell.V H ≤ centralizer (pCore 2 H : Set H) := by
    rw [h.campbellV_eq_moved hB m]
    exact h.moved_le_coreOmegaCenter.trans
      (fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).2.2)
  intro v hv
  apply mem_center_iff.mpr
  intro g
  have hg : g ∈ Campbell.J (⊤ : Subgroup H) ⊔ pCore 2 H := by
    rw [InLocalClass.global_thompson_sup_core_eq_top h hB]
    exact mem_top g
  obtain ⟨k,hk,q,hq,rfl⟩ := mem_sup_of_normal_right.mp hg
  have hkcomm := hv.2 k hk
  have hqcomm := hVC hv.1 q hq
  calc
    (k*q)*v = k*(q*v) := mul_assoc _ _ _
    _ = k*(v*q) := by rw [hqcomm]
    _ = (k*v)*q := (mul_assoc _ _ _).symm
    _ = (v*k)*q := by rw [hkcomm]
    _ = v*(k*q) := mul_assoc _ _ _

/-- The actual middle conjugation on a span, transported back through the
restricted Sylow automorphism. -/
@[expose] def spanConjugationMap (W W' : Subgroup H) (a : W' ≃* W)
    (u : normalizer (W : Set H)) : W' →* H :=
  W'.subtype.comp ((a.trans (W.normalizerMonoidHom u)).trans a.symm).toMonoidHom

theorem InLocalClass.involution_conjugate_commutes_of_span_transport (hL : InLocalClass e) (hB : IsBaumannFixed B)
    (W W' Z : Subgroup H) (hW : IsPGroup 2 W) (hW' : IsPGroup 2 W')
    (a : W' ≃* W) (u : normalizer (W : Set H))
    (hu : (u : H) ∈ Campbell.J (⊤ : Subgroup H))
    (hZ : Z ≤ centralizer (Campbell.J (⊤ : Subgroup H) : Set H))
    (hPhiW : (frattini W).map W.subtype ≤ Z)
    (hPhiW' : (frattini W').map W'.subtype ≤ Campbell.V H)
    (g : W') (h : H) (hg2 : g^2=1) (hh2 : h^2=1) (hh : h ∈ W)
    (hgN : (g : H) ∈ normalizer (W : Set H)) (hhN : h ∈ normalizer (W' : Set H))
    (hfg : spanConjugationMap W W' a u g ∈ Campbell.V H) :
    ⁅h,(g:H)*h*(g:H)⁻¹⁆=1 := by
  let f := spanConjugationMap W W' a u
  have hf : Function.Injective f := W'.subtype_injective.comp
    (((a.trans (W.normalizerMonoidHom u)).trans a.symm).injective)
  apply private_involution_consumer hL hB W W' hW hW' f hf ?_ g h hg2 hh2 hh hgN hhN hfg
  intro z hzW hzW'
  have haz : W.normalizerMonoidHom u (a z) = a z := by
    apply Subtype.ext
    change (u : H)*(a z : H)*(u:H)⁻¹=(a z : H)
    have hazPhi : a z ∈ frattini W :=
      frattini_le_comap_frattini_of_surjective (φ := a.toMonoidHom) a.surjective hzW'
    have hcomm : (u : H)*(a z : H)=(a z : H)*(u : H) :=
      hZ (hPhiW (mem_map_of_mem W.subtype hazPhi)) u hu
    rw [hcomm,mul_inv_cancel_right]
  have hfz : f z = (z : H) := by
    change (a.symm (W.normalizerMonoidHom u (a z)) : H) = z
    rw [haz,a.symm_apply_apply]
  rw [hfz]
  exact InLocalClass.campbell_centralizer_global_thompson_le_center hL hB ⟨hPhiW' (mem_map_of_mem W'.subtype hzW'),hZ (hPhiW hzW)⟩

end CFSG.Quasithin.ChapterC.GlaubermanNiles
