module

public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.SylowSupplement

-- Continue the internal construction of J from Structure, proving its public
-- normality instance without exposing the implementation of that definition.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The two-residual of a minimal parabolic

For K = O²(H), the finite residual/Sylow theorem proves H = KT. It supplies
the factorization premise in the existing proof of K ≰ J, completing the
remaining assertion of B.6.8(1). If a normal Y is outside J, the unique
maximal-overgroup argument gives H = YT. Hence H/Y is a two-group and
K ≤ Y, which is precisely B.6.8(4).

The star quotient is the original H/J and its Sylow subgroup is the image
of T under that quotient map. Its residual is the image of K and is
nontrivial. The canonical isomorphism uses K/(K ∩ J); no inclusion J ≤ K
is assumed. Residual transport to the other source quotient H/O₂(H) is
also recorded. These results do not require solvability or model recognition.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.6.8 and its proof, printed pp.113–115.
-/

public section
namespace CFSG.Quasithin.ChapterB
variable {H : Type*} [Group H]

/-- The source's K = O²(H), distinct from its two-core O₂(H). Normality and
characteristicity are inherited from the prime-residual API. -/
abbrev minimalParabolicResidual : Subgroup H := pResidual 2 H

/-- J is normal in H, since it is the normal core of the maximal overgroup. -/
instance minimalParabolicCore_normal (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) : (minimalParabolicCore T hP).Normal := by
  unfold minimalParabolicCore
  infer_instance

variable [Finite H]

/-- The factorization H = KT is a theorem for every finite group and its
Sylow two-subgroup, without an additional minimal-parabolic hypothesis. -/
theorem minimalParabolic_residual_sup_sylow (T : Sylow 2 H) :
    minimalParabolicResidual (H := H) ⊔ (T : Subgroup H) = ⊤ :=
  Subgroup.pResidual_sup_sylow_eq_top T

/-- The residual assertion of B.6.8(1), with its factorization premise discharged. -/
theorem minimalParabolic_residual_not_le_core (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    ¬ minimalParabolicResidual (H := H) ≤ minimalParabolicCore T hP := by
  apply minimalParabolic_residual_not_le_core_of_factorization T hP
  simpa only [sup_comm] using minimalParabolic_residual_sup_sylow T

/-- B.6.8(4): a normal subgroup is contained in J or contains K = O²(H). -/
theorem minimalParabolic_normal_subgroup_residual_dichotomy (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (Y : Subgroup H) [Y.Normal] :
    Y ≤ minimalParabolicCore T hP ∨ minimalParabolicResidual (H := H) ≤ Y := by
  rcases minimalParabolic_normal_subgroup_dichotomy T hP Y with hY | hY
  · exact Or.inl hY
  · right
    apply (Subgroup.pResidual_le_iff_isPGroup_quotient 2 Y).mpr
    exact Subgroup.isPGroup_quotient_of_sup_eq_top Y T T.isPGroup'
      (by simpa only [sup_comm] using hY)

/-- The source's T* is the Sylow image under the actual map H → H/J. -/
noncomputable def minimalParabolicStarSylow (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) : Sylow 2 (minimalParabolicStarQuotient T hP) :=
  T.mapSurjective (QuotientGroup.mk'_surjective (minimalParabolicCore T hP))

/-- The underlying subgroup of T* is the image of T. -/
theorem minimalParabolicStarSylow_coe (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    (minimalParabolicStarSylow T hP : Subgroup (minimalParabolicStarQuotient T hP)) =
      (T : Subgroup H).map (QuotientGroup.mk' (minimalParabolicCore T hP)) := by
  rfl

/-- K* is the two-residual of the literal star quotient H/J. -/
theorem minimalParabolic_residual_star_image (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    minimalParabolicResidual.map (QuotientGroup.mk' (minimalParabolicCore T hP)) =
      pResidual 2 (minimalParabolicStarQuotient T hP) :=
  Subgroup.map_pResidual_quotient 2 (minimalParabolicCore T hP)

/-- Pulling back the star residual gives KJ, with both factors retained. -/
theorem minimalParabolic_residual_star_preimage (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    (pResidual 2 (minimalParabolicStarQuotient T hP)).comap
        (QuotientGroup.mk' (minimalParabolicCore T hP)) =
      minimalParabolicResidual ⊔ minimalParabolicCore T hP :=
  Subgroup.comap_pResidual_quotient 2 (minimalParabolicCore T hP)

/-- K/(K ∩ J) is canonically the residual of H/J. -/
noncomputable def minimalParabolicResidualStarEquiv (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    (minimalParabolicResidual (H := H) ⧸
      (minimalParabolicCore T hP).subgroupOf minimalParabolicResidual) ≃*
        pResidual 2 (minimalParabolicStarQuotient T hP) :=
  Subgroup.pResidualQuotientEquiv 2 (minimalParabolicCore T hP)

/-- The star residual identification commutes with the original quotient map. -/
@[simp] theorem minimalParabolicResidualStarEquiv_mk (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (x : minimalParabolicResidual (H := H)) :
    ((minimalParabolicResidualStarEquiv T hP
      (QuotientGroup.mk' ((minimalParabolicCore T hP).subgroupOf minimalParabolicResidual) x) :
        pResidual 2 (minimalParabolicStarQuotient T hP)) : minimalParabolicStarQuotient T hP) =
          QuotientGroup.mk' (minimalParabolicCore T hP) x :=
  Subgroup.pResidualQuotientEquiv_mk 2 (minimalParabolicCore T hP) x

/-- The residual in the star quotient is nontrivial. -/
theorem minimalParabolic_residual_star_ne_bot (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    pResidual 2 (minimalParabolicStarQuotient T hP) ≠ ⊥ := by
  intro h
  rw [← minimalParabolic_residual_star_image T hP, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at h
  exact minimalParabolic_residual_not_le_core T hP h

/-- H* = K*T*, using the transported residual and the actual Sylow image. -/
theorem minimalParabolic_residual_star_sup_sylow (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) :
    pResidual 2 (minimalParabolicStarQuotient T hP) ⊔
      (minimalParabolicStarSylow T hP : Subgroup (minimalParabolicStarQuotient T hP)) = ⊤ :=
  Subgroup.pResidual_sup_sylow_eq_top (minimalParabolicStarSylow T hP)

/-- Residual transport through the other source quotient, H/O₂(H). -/
theorem minimalParabolic_residual_twoCore_image :
    minimalParabolicResidual.map (QuotientGroup.mk' (minimalParabolicTwoCore (H := H))) =
      pResidual 2 (minimalParabolicQuotient (H := H)) :=
  Subgroup.map_pResidual_quotient 2 minimalParabolicTwoCore

end CFSG.Quasithin.ChapterB
end
