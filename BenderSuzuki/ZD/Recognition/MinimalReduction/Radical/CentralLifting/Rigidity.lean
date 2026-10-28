module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Cover
public import Theory.GroupTheory.PerfectCentralCoverSylowRigidity
public import Theory.GroupTheory.CenterQuotientIrreducible
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Reduction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.QuotientInner
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.Linear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.ModelActions
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.SuzukiActions
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.DirectSylowCenters.UnitaryActions

/-!
# Sylow-centralizer rigidity for Bender double covers

For a perfect central cover of an actual simple Bender model, its kernel is
its whole center. A kernel of order two therefore gives precisely the
nontrivial central two-subgroup in every Sylow two-subgroup, as required by
the standing hypotheses of GLS, Volume 4, Chapter 4, Section 2.

The original local-data theorem combines quotient pointwise innerness and
a covering Sylow-center bound using uniqueness for perfect covers. The
generic double Suzuki quotient-center argument is re-exported from
`CenterQuotientIrreducible`.

The actual PSL₂, Suzuki and unitary normalizer actions identify every covering
Sylow center with the original covering kernel. Together with uniform quotient
innerness this proves that every automorphism fixing that Sylow pointwise is
the identity. All concrete action premises are discharged, including the
Sz(8) and PSU₃(4) parameters. The result applies to the literal covering
component in the central-quotient reduction for Theorem ZD.

Source: GLS, Volume 4, Chapter 4, Lemma 2.8(c), restricted to central kernels
of order two; its application is Chapter 2, Lemma 4.5. The direct proof uses
transfer and torus actions without classifying the covering groups.
-/

namespace BenderSuzuki.ZD

variable {E B : Type*} [Group E] [Group B] [Finite B]

/-- A simple Bender group has trivial center. -/
public theorem bender_center_eq_bot (hB : IsSimpleBenderGroup B) :
    Subgroup.center B = ⊥ := by
  let : IsSimpleGroup B := hB.isSimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center B) inferInstance with h | h
  · exact h
  · exact (hB.not_commutative (fun x y => by
      have hx : x ∈ Subgroup.center B := h ▸ Subgroup.mem_top x
      exact (Subgroup.mem_center_iff.mp hx y).symm)).elim

/-- The covering kernel is the whole center, not merely a central subgroup. -/
public theorem bender_cover_ker_eq_center (hB : IsSimpleBenderGroup B)
    (f : PerfectCentralCovering.Cover E B) :
    f.toMonoidHom.ker = Subgroup.center E := by
  rw [← f.comap_center, bender_center_eq_bot hB]
  rfl

/-- A Bender double cover has center of order two. -/
public theorem bender_double_cover_center_card (hB : IsSimpleBenderGroup B)
    (f : PerfectCentralCovering.Cover E B) (hcard : Nat.card f.toMonoidHom.ker = 2) :
    Nat.card (Subgroup.center E) = 2 := by
  rwa [← bender_cover_ker_eq_center hB f]

/-- Its whole center is contained in every Sylow two-subgroup. -/
public theorem bender_double_cover_center_le_sylow (hB : IsSimpleBenderGroup B)
    (f : PerfectCentralCovering.Cover E B) (hcard : Nat.card f.toMonoidHom.ker = 2)
    (P : Sylow 2 E) : Subgroup.center E ≤ P := by
  have hp : IsPGroup 2 (Subgroup.center E) :=
    IsPGroup.of_card (n := 1) (by simpa using bender_double_cover_center_card hB f hcard)
  exact hp.le_sylow_of_normal P

variable [Finite E]

/-- Conditional final transfer: the source's two independent local calculations
imply rigidity for this actual perfect cover. Neither calculation is assumed to
follow merely from the Bender family predicate. -/
public theorem bender_cover_fixingSylow_eq_one_of_local_data
    (hB : IsSimpleBenderGroup B) (f : PerfectCentralCovering.Cover E B)
    (P : Sylow 2 E)
    (hcenter : (Subgroup.center P).map (P : Subgroup E).subtype ≤ f.toMonoidHom.ker)
    (hinner : ∀ (Q : Sylow 2 B) (β : MulAut B),
      (∀ b ∈ Q, β b = b) → ∃ b ∈ Q, β = MulAut.conj b)
    (α : MulAut E) (hfix : ∀ x : P, α (x : E) = x) : α = 1 := by
  apply f.fixing_eq_one_of_image_inner (bender_cover_ker_eq_center hB f)
    (P : Subgroup E) hcenter
  · intro β hβ
    have hm : (P.mapSurjective f.surjective : Subgroup B) =
        (P : Subgroup E).map f.toMonoidHom := Sylow.coe_mapSurjective _ _
    obtain ⟨b, hb, he⟩ := hinner (P.mapSurjective f.surjective) β (by
      change ∀ b ∈ (P.mapSurjective f.surjective : Subgroup B), β b = b
      rwa [hm])
    change b ∈ (P.mapSurjective f.surjective : Subgroup B) at hb
    exact ⟨b, hm ▸ hb, he⟩
  · intro x hx
    exact hfix ⟨x, hx⟩

/-- Uniform quotient innerness removes the automorphism premise: only the
covering Sylow-center bound remains. -/
public theorem bender_cover_fixingSylow_eq_one_of_center_bound
    (hB : IsSimpleBenderGroup B) (f : PerfectCentralCovering.Cover E B)
    (P : Sylow 2 E)
    (hcenter : (Subgroup.center P).map (P : Subgroup E).subtype ≤ f.toMonoidHom.ker)
    (α : MulAut E) (hfix : ∀ x : P, α (x : E) = x) : α = 1 :=
  bender_cover_fixingSylow_eq_one_of_local_data hB f P hcenter
    (DirectSylowCenters.bender_aut_fixing_sylow_inner hB) α hfix

/-- Conditional direct assembly of the exact center equality. The two
remaining inputs concern only the actual base-model normalizer actions. -/
public theorem bender_double_cover_sylow_center_of_torus_actions
    (hSuzuki : DirectSylowCenters.SuzukiCenterActions)
    (hUnitary : DirectSylowCenters.UnitaryCenterActions)
    (hB : IsSimpleBenderGroup B) (f : PerfectCentralCovering.Cover E B)
    (hcard : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E) :
    (Subgroup.center P).map (P : Subgroup E).subtype = f.toMonoidHom.ker := by
  have hs := hB.isSimple
  rcases hB with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
    ⟨⟨n, hn, K, hK, hKfin, J, hJ, hKcard, hfixed, ⟨e⟩⟩⟩
  · exact DirectSylowCenters.linear_cover_sylow_center f hcard e P
  · obtain ⟨Q, hQ⟩ := hSuzuki m hm
    exact f.sylow_center_eq_kernel_of_model_sylow hcard e Q hQ P
  · let : IsSimpleGroup B := hs
    let : Finite (_root_.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_equiv B e.toEquiv
    let : IsSimpleGroup (_root_.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      e.symm.isSimpleGroup
    obtain ⟨Q, hQ⟩ := hUnitary K J n hn hJ hKcard hfixed
    exact f.sylow_center_eq_kernel_of_model_sylow hcard e Q hQ P

/-- The original universal rigidity follows once the two concrete torus
calculations have been supplied; no cover-classification premise is used. -/
public theorem bender_cover_fixingSylow_eq_one_of_torus_actions
    (hSuzuki : DirectSylowCenters.SuzukiCenterActions)
    (hUnitary : DirectSylowCenters.UnitaryCenterActions)
    (hB : IsSimpleBenderGroup B) (f : PerfectCentralCovering.Cover E B)
    (hcard : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E)
    (α : MulAut E) (hfix : ∀ x : P, α (x : E) = x) : α = 1 :=
  bender_cover_fixingSylow_eq_one_of_center_bound hB f P
    (bender_double_cover_sylow_center_of_torus_actions hSuzuki hUnitary hB f hcard P).le
    α hfix

/-- The center of every Sylow two-subgroup of a perfect central Bender double
cover is exactly the kernel of the given covering map. All three model action
calculations are supplied, with their original parameter guards. -/
public theorem bender_double_cover_sylow_center
    (hB : IsSimpleBenderGroup B) (f : PerfectCentralCovering.Cover E B)
    (hcard : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E) :
    (Subgroup.center P).map (P : Subgroup E).subtype = f.toMonoidHom.ker :=
  bender_double_cover_sylow_center_of_torus_actions
    DirectSylowCenters.suzuki_center_actions DirectSylowCenters.unitary_center_actions
    hB f hcard P

/-- The Sylow-center assertion of GLS4, Chapter 4, Lemma 2.8(c), for perfect
central double covers, with both centers viewed inside the covering group. -/
public theorem bender_double_cover_sylow_center_eq_center
    (hB : IsSimpleBenderGroup B) (f : PerfectCentralCovering.Cover E B)
    (hcard : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E) :
    (Subgroup.center P).map (P : Subgroup E).subtype = Subgroup.center E :=
  (bender_double_cover_sylow_center hB f hcard P).trans (bender_cover_ker_eq_center hB f)

/-- Universal Sylow-centralizer rigidity for genuine perfect central double
covers of simple Bender groups. The automorphism has arbitrary order and the
Sylow subgroup is the caller's actual subgroup of the covering group. -/
public theorem bender_cover_fixingSylow_eq_one
    (hB : IsSimpleBenderGroup B) (f : PerfectCentralCovering.Cover E B)
    (hcard : Nat.card f.toMonoidHom.ker = 2) (P : Sylow 2 E)
    (α : MulAut E) (hfix : ∀ x : P, α (x : E) = x) : α = 1 :=
  bender_cover_fixingSylow_eq_one_of_center_bound hB f P
    (bender_double_cover_sylow_center hB f hcard P).le α hfix

section SourceApplication
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Apply the direct route to the literal covering component in ZD's
central-involution reduction. The two base-action calculations are the only
new premises beyond the original central-quotient setup. -/
public theorem central_quotient_component_simple_of_torus_actions
    (hSuzuki : DirectSylowCenters.SuzukiCenterActions)
    (hUnitary : DirectSylowCenters.UnitaryCenterActions)
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hcentral : ∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G))
    (hodd : pPrimeCore 2 G = ⊥)
    (A : Subgroup G) [A.Normal] (hAc : A ≤ Subgroup.center G) (hAcard : Nat.card A = 2)
    (hs : StructureConclusion ((QuotientGroup.mk' A) '' Z) (M.map (QuotientGroup.mk' A))) :
    IsSimpleGroup (centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A))) := by
  have hD := central_quotient_derived_model hgen hodd A hAc hAcard hs
  apply central_quotient_component_simple_of_rigidity h hgen hcentral hodd A hAc hAcard hs
  intro hcard P α hfix
  exact bender_cover_fixingSylow_eq_one_of_torus_actions hSuzuki hUnitary hD
    (centralLiftCover (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A)
      (by simpa only [QuotientGroup.ker_mk'] using hAc) (commutator (G ⧸ A)) hD)
    hcard P α hfix

/-- Apply universal rigidity to the original central-quotient covering
component. This discharges the rigidity premise in the nonsimple branch of
GLS4, Chapter 2, Lemma 4.5, without any additional model or action premise. -/
public theorem central_quotient_component_simple
    (h : IsProductDisconnected Z M) (hgen : Subgroup.closure Z = ⊤)
    (hcentral : ∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G))
    (hodd : pPrimeCore 2 G = ⊥)
    (A : Subgroup G) [A.Normal] (hAc : A ≤ Subgroup.center G) (hAcard : Nat.card A = 2)
    (hs : StructureConclusion ((QuotientGroup.mk' A) '' Z) (M.map (QuotientGroup.mk' A))) :
    IsSimpleGroup (centralLiftComponent (QuotientGroup.mk' A) (commutator (G ⧸ A))) := by
  have hD := central_quotient_derived_model hgen hodd A hAc hAcard hs
  apply central_quotient_component_simple_of_rigidity h hgen hcentral hodd A hAc hAcard hs
  intro hcard P α hfix
  exact bender_cover_fixingSylow_eq_one hD
    (centralLiftCover (QuotientGroup.mk' A) (QuotientGroup.mk'_surjective A)
      (by simpa only [QuotientGroup.ker_mk'] using hAc) (commutator (G ⧸ A)) hD)
    hcard P α hfix

end SourceApplication

end BenderSuzuki.ZD
