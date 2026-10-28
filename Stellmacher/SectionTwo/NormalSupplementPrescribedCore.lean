module
public import Stellmacher.SectionTwo.NormalSupplementBaumannSetup
public import Stellmacher.SectionTwo.NormalSupplementBaumannDecomposition
public import Stellmacher.SectionTwo.PrescribedModuleCoreBound
public import Stellmacher.SectionThree.LemmaThreeFour
public import Theory.GroupTheory.SylowImageIntersection
/-!
# A prescribed core bound across a normal supplement

In the finite Section Two and Section Three setup, let N be a normal Sylow
supplement whose supplied Sylow image Q is normalized by S and contains
Omega1(Z(S)). Assume O2(G)=C_S(V) for the original module V=vSubgroup S.
If the Baumann subgroup B of Q lies outside O2(G), and all generating local
groups with supplied Sylow image B satisfy the characteristic obstruction,
then [O2(G),O2-residual(G)] lies in that original V.

The normal-supplement Baumann theorem puts V in B and makes B Sylow in its
normal closure L. Since B is normal in S and lies outside the core, (3.4)
puts the residual in L, whence L S=G. The faithful original-module quotient
has nontrivial B-image and the normal-supplement action decomposition gives
its exact SL2(2) product. The prescribed-module pushing-up bound applies to
this same quotient and module, using the supplied local characteristic
obstruction and the proved Sylow image-intersection identity.

This expands the (2.3),(2.4) normal-supplement argument used in Stellmacher
(8.3), Journal of Algebra 190 (1997), p38, refs/latex/stellmacher-n-group.tex.
It avoids identifying the original center closure with the different closure
of the smaller Sylow subgroup. The local pushing-up structure retains the
nested Frattini quotient in its imported theorem.
-/

namespace Stellmacher.SectionTwo
universe u
/-- The original module bounds the core-residual commutator across a normal supplement. -/
public theorem normal_supplement_core_residual_le_module
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (h3 : SectionThree.Hypotheses G (S : Subgroup G))
    (hP : (⊤ : Subgroup G) ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G))
    (N : Subgroup G) [N.Normal] (Q : Sylow 2 N)
    (hgen : N ⊔ (S : Subgroup G) = ⊤)
    (hQS : (Q : Subgroup N).map N.subtype ≤ (S : Subgroup G))
    (hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (((Q : Subgroup N).map N.subtype : Subgroup G) : Set G))
    (hZQ : zSubgroup S ≤ (Q : Subgroup N).map N.subtype)
    (hQne : (Q : Subgroup N) ≠ ⊥)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (hBnot : ¬ (Q : Subgroup N).map N.subtype ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ ((Q : Subgroup N).map N.subtype)) : Set G) ≤ pCore 2 G)
    (hcharacteristic : ∀ (K : Subgroup G) (PK : Sylow 2 K),
      (PK : Subgroup K).map K.subtype =
        (Q : Subgroup N).map N.subtype ⊓ Subgroup.centralizer
          (omegaOneCenterAmbient (elementaryAbelianMaxJ ((Q : Subgroup N).map N.subtype)) : Set G) →
      K ⊔ (S : Subgroup G) = ⊤ →
      ∀ A : Subgroup PK, A.Characteristic → A ≠ ⊥ →
        ¬ (A.map (PK : Subgroup K).subtype).Normal) :
    ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ vSubgroup S := by
  classical
  let _ : Group.IsSolvable G := h.solvable
  let QA := (Q : Subgroup N).map N.subtype
  let B := QA ⊓ Subgroup.centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ QA) : Set G)
  let L := Subgroup.normalClosure (B : Set G)
  let V := vSubgroup S
  let _ : V.Normal := Subgroup.normalClosure_normal
  let _ : L.Normal := Subgroup.normalClosure_normal
  have hBsetup := normal_supplement_baumann_setup h S N Q hgen hQS hSN hZQ hQne hcore
  have hVB : V ≤ B := hBsetup.1
  obtain ⟨PL,hPL⟩ := hBsetup.2
  have hBS : B ≤ (S : Subgroup G) := inf_le_left.trans hQS
  have hSB : (S : Subgroup G) ≤ Subgroup.normalizer (B : Set G) :=
    hSN.trans (normalizer_le_normalizer_baumann QA)
  have hBN : (B.subgroupOf (S : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).mpr hSB
  have htopCore : twoCoreAmbient (⊤ : Subgroup G) = pCore 2 G := by
    exact pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
  have hcomm : ⁅twoResidualAmbient (⊤ : Subgroup G),B⁆ = twoResidualAmbient (⊤ : Subgroup G) := by
    apply (SectionThree.lemma_three_four (S : Subgroup G) h3 ⊤ hP B ⟨hBS,hBN⟩ inferInstance).resolve_left
    rwa [htopCore]
  have hRL : twoResidualAmbient (⊤ : Subgroup G) ≤ L := by
    rw [← hcomm]
    exact (Subgroup.commutator_mono le_rfl (show B ≤ L from Subgroup.le_normalClosure)).trans
      (Subgroup.commutator_le_right _ _)
  have hLgen : L ⊔ (S : Subgroup G) = ⊤ := by
    apply top_unique
    rw [← twoResidualAmbient_top_sup_sylow S]
    exact sup_le_sup_right hRL _
  let C := cSubgroup S
  let _ : C.Normal := Subgroup.normal_centralizer
  let q := QuotientGroup.mk' C
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective C
  have hker : q.ker = cSubgroup S := QuotientGroup.ker_mk' C
  have hBne : B.map q ≠ ⊥ := by
    intro hb
    apply hBnot
    rw [hcore]
    exact le_inf hBS ((Subgroup.map_eq_bot_iff B).mp hb |>.trans_eq hker)
  have hdata := normal_supplement_baumann_decomposition h S q hq hker N Q
    hgen hSN (hVB.trans inf_le_left)
  change BaumannFactorModuleData V L q at hdata
  obtain ⟨n,D,_Vf,_hDgen,hprod,hSL,_hVf,_hVprod⟩ := hdata.factors
  exact core_residual_le_prescribed_module h.solvable S V L B
    (vSubgroup_le_twoCore_and_elementaryAbelian h S).2 hVB hBS PL hPL hLgen hP.2
    q hq hker hBne (Sylow.map_image_eq_inf S L B PL hPL hBS q) D hprod hSL hcharacteristic
end Stellmacher.SectionTwo

