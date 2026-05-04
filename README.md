# SpatCausal
This repository contains code for the paper "Spatial causal inference in the presence of preferential sampling to study the impacts of marine protected areas" accepted for publication in AOAS (2026).

**Overview**

The repository is organized to support both simulation studies and real data analysis presented in the paper. It includes:

	•	R scripts for fitting the proposed models
	
	•	Folders with links to external simulation datasets
	
  	•	An R Markdown file to reproduce the real data analysis using a synthetic data

**Model Implementation**

The models used in the paper can be run using the following R scripts:

	•	final_func.R — implements the proposed (referred to as "Full" in the paper) model along with "Naive" and "Shared"
	
	•	ps_adj.R — implements the propensity score adjustment referred to as "PSA-B" and "PSA-G" in the paper

The scripts are structured with dictionaries for the arguments of each function.

**Simulation Study**

Simulation study results rely on datasets that are hosted externally due to their size.

	•	The folder named simulation_data in this repository contains a link to the corresponding Dropbox folder with the data. To evaluate bias, mean squared error (MSE), and 95% credible intervals, use _posterior_analysis.R_ in each folder.

**Real Data Analysis**

The dataset used for the real data applications in the paper is not publicly available due to confidentiality restrictions. To replicate the real data analysis using a synthetic data, see _Example.Rmd_


