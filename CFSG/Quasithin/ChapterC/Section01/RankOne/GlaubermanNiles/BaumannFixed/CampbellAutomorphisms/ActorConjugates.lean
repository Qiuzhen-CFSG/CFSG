module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.PointCentralizers
public import Theory.GroupTheory.PointCentralizerConjugates
/-!
# Commuting natural-module conjugates under the source actors

The original local group has a natural point outside the Sylow fixed
subgroup: otherwise the Sylow would lie in the kernel and equal O₂(H),
contrary to minimal parabolicity. Transporting its exact point-centralizer
through α∈Aut(S) and conjugation gives a detector for every (V^α)^g.

For the actual W and W′ of II.6.2, an actor x whose transported image lies
in V is an involution, and every involution y∈W commutes with yˣ. Applying
the point detector proves [(V^α)^g,((V^α)^g)^x]=1 for all g∈J(H).
All normalizers, point selection and module coordinates come from the
original local-class and Baumann-fixed hypotheses. The subsequent source
step choosing such an actor to represent an arbitrary element of S modulo
the core, and upgrading V-conjugates to F-conjugates, remains separate.
Source: Campbell II.6.3, printed pp.30–31, for the Aut(S) corollary.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

theorem InLocalClass.exists_campbell_nonfixed_point (h : InLocalClass e) (hB : IsBaumannFixed B) :
    ∃ v ∈ Campbell.V H, v ∉ centralizer (e.range : Set H) := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨_,_,_,_,_,_,_,hC⟩ := h.exists_faithful_natural_action m
  by_contra hn
  push Not at hn
  have hSC : e.range ≤ centralizer (Campbell.V H : Set H) := le_centralizer_iff.mp hn
  rw [h.campbellV_eq_moved hB m,hC] at hSC
  have hSK := d.sylow_inf_eq_core _ h.core_le_localKernel h.kernel_noPartialComplement
  have hEQ : (d.sylow : Subgroup H)=pCore 2 H :=
    (inf_eq_left.mpr (hS ▸ hSC)).symm.trans hSK
  obtain ⟨T,hT,hP⟩ := h.sylow
  apply (ChapterB.isMinimalParabolicOver_top_iff T).mp hP |>.2
  have ht : (T:Subgroup H)=pCore 2 H := hT.symm.trans (hS.symm.trans hEQ)
  rw [ht]
  infer_instance

variable (S : Subgroup H)
theorem InLocalClass.automorphism_conjugate_point_centralizer (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S) (v : S)
    (hv : (v:H) ∈ Campbell.V H) (hvS : (v:H) ∉ centralizer (S : Set H)) (g : H) :
    pCore 2 H ⊓ centralizer ({g*(a v:H)*g⁻¹} : Set H) =
      pCore 2 H ⊓ centralizer ((automorphismImage S a (Campbell.V H)).map
        (MulAut.conj g).toMonoidHom : Set H) := by
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hSet : (S:Set H)=(T:Set H) := congrArg (fun X : Subgroup H => (X:Set H)) hST
  have hpt := h.campbell_point_centralizer hB T v hv (by rwa [←hSet])
  rw [←hST] at hpt
  have haut := automorphism_point_centralizer S (Campbell.V H) a v hv hpt
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  have hQpt : pCore 2 H ⊓ centralizer ({(a v:H)} : Set H) =
      pCore 2 H ⊓ centralizer (automorphismImage S a (Campbell.V H) : Set H) := by
    calc
      _ = pCore 2 H ⊓ (S ⊓ centralizer ({(a v:H)} : Set H)) := by rw [←inf_assoc,inf_eq_left.mpr hQS]
      _ = pCore 2 H ⊓ (S ⊓ centralizer (automorphismImage S a (Campbell.V H) : Set H)) := congrArg (fun X => pCore 2 H ⊓ X) haut
      _ = _ := by rw [←inf_assoc,inf_eq_left.mpr hQS]
  exact point_centralizer_conjugate (pCore 2 H) (automorphismImage S a (Campbell.V H)) g (a v)
    (le_normalizer_of_normal (mem_top g))
    (mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom hv)) hQpt

theorem InLocalClass.sylow_automorphism_actor_conjugates (hL : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H) :
    let W := conjugateSpanBy (automorphismImage S a (Campbell.F H)) (Campbell.J (⊤ : Subgroup H))
    let W' := automorphismImage S a.symm W
    ∃ b : W' ≃* W,
      (∀ w : W', (b w : H) = (a ⟨w,automorphismImage_le S a.symm W w.property⟩ : H)) ∧
      ∀ u : normalizer (W : Set H), (u : H) ∈ Campbell.J (⊤ : Subgroup H) →
        ∀ x : W', spanConjugationMap W W' b u x ∈ Campbell.V H →
          ∀ g ∈ Campbell.J (⊤ : Subgroup H),
            let A := (automorphismImage S a (Campbell.V H)).map (MulAut.conj g).toMonoidHom
            ⁅A,A.map (MulAut.conj (x:H)).toMonoidHom⁆=⊥ := by
  let Y := automorphismImage S a (Campbell.F H)
  let K := Campbell.J (⊤ : Subgroup H)
  let W := conjugateSpanBy Y K
  let W' := automorphismImage S a.symm W
  obtain ⟨b,hb,hi⟩ := hL.sylow_automorphism_involutions S hB a hV
  refine ⟨b,hb,?_⟩
  intro u hu x hx g hg
  let A := (automorphismImage S a (Campbell.V H)).map (MulAut.conj g).toMonoidHom
  have hs := hL.sylow_automorphism_span S hB a hV
  have hAW : A ≤ W := by
    rintro z ⟨v,hv,rfl⟩
    apply (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy Y K hg) v).mp
    exact le_conjugateSpanBy Y K (automorphismImage_mono S a Campbell.V_le_F hv)
  obtain ⟨v,hv,hvn⟩ := hL.exists_campbell_nonfixed_point hB
  obtain ⟨T,hT,_⟩ := hL.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hQS : pCore 2 H ≤ S := hST ▸ pCore_isPGroup.le_sylow_of_normal T
  let vs : S := ⟨v,Campbell.V_le_pCore.trans hQS hv⟩
  have hvn' : v ∉ centralizer (S:Set H) := by simpa only [range_subtype] using hvn
  let y : H := g*(a vs:H)*g⁻¹
  have hyA : y ∈ A := mem_map_of_mem (MulAut.conj g).toMonoidHom
    (mem_map_of_mem S.subtype (mem_map_of_mem a.toMonoidHom hv))
  have hy2 : y^2=1 := by
    let : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 H)) := omegaOneCenterAmbient_elementaryAbelian _
    have hv2 : v^2=1 := elemPow_eq_one_of_isElementaryAbelian _ (Campbell.V_le_omegaCore hv)
    have hvs2 : vs^2=1 := Subtype.ext hv2
    have has2 : (a vs)^2=1 := by rw [←map_pow,hvs2,map_one]
    have ha2 : (a vs:H)^2=1 := congrArg Subtype.val has2
    change ((MulAut.conj g) (a vs:H))^2=1
    rw [←map_pow,ha2,map_one]
  have hx2 : x^2=1 := by
    have hf : Function.Injective (spanConjugationMap W W' b u) := W'.subtype_injective.comp
      (((b.trans (W.normalizerMonoidHom u)).trans b.symm).injective)
    apply hf
    rw [map_pow,map_one]
    let : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 H)) := omegaOneCenterAmbient_elementaryAbelian _
    exact elemPow_eq_one_of_isElementaryAbelian _ (Campbell.V_le_omegaCore hx)
  exact conjugates_commute_of_point_centralizer (pCore 2 H) A (hAW.trans hs.1) x y
    (le_normalizer_of_normal (mem_top (x:H))) (congrArg Subtype.val hx2) (hs.1 (hAW hyA))
    (hL.automorphism_conjugate_point_centralizer S hB a vs hv hvn' g)
    (hi u hu x hx y (hAW hyA) hy2)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
